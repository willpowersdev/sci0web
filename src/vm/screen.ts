/**
 * The SCI0 screen: three 320x190 planes and the rules for drawing on them.
 *
 * A picture paints all three -- what you see, how near it is, and what
 * the floor does there.  Everything drawn afterwards is transient: cels
 * are composited over a saved copy of the background each frame rather
 * than erased individually, which is both simpler and what the
 * interpreter effectively did with its "restore under bits" bookkeeping.
 *
 * A cel pixel is drawn only where its priority is at least the priority
 * already there, which is what beds an actor into the scenery instead of
 * pasting it on top.
 */
import { type Picture, WIDTH, HEIGHT } from '../pic.ts';
import type { Cel } from '../view.ts';
import type { Font } from '../font.ts';
import { EGA_RGB, BLENDED_RGB, ditherPixel } from '../ega.ts';
import { histogram } from '../undither.ts';
import { type Cursor, CURSOR_SIZE, CURSOR_CLEAR } from '../font.ts';

export { WIDTH, HEIGHT };
/** The status line sits above the picture; SCI0 reserves ten rows. */
export const STATUS_HEIGHT = 10;
export const SCREEN_HEIGHT = HEIGHT + STATUS_HEIGHT;

/**
 * The styles a picture can arrive in, after SCI0's numbering is
 * translated.
 *
 * `DrawPic`'s second argument carries the number in its low byte, and
 * ScummVM keeps a table turning the old numbers into these -- 0 and 1
 * are the rolls, 2 to 5 the straight wipes, 8 blocks, 9 and 10 the
 * rolls closing instead of opening, 18 the pixel dissolve, 30 a fade,
 * and 100 no transition at all.  11 to 17 are 2 to 8 again with the
 * blackout flag, which plays the opposite wipe to black first.
 */
/**
 * The ways a picture can arrive, named as ScummVM names them.
 *
 * A roll opens from the middle or closes onto it; a straight wipe is one
 * edge sweeping across; a diagonal roll is all four edges at once, which
 * is a square growing out of the centre or shrinking onto it; a scroll
 * pushes the old picture off the side as the new one follows it on.
 */
export type Wipe = 'none' | 'pixels' | 'blocks' | 'fade'
  | 'straight-from-left' | 'straight-from-right'
  | 'straight-from-top' | 'straight-from-bottom'
  | 'vroll-from-centre' | 'vroll-to-centre'
  | 'hroll-from-centre' | 'hroll-to-centre'
  | 'droll-from-centre' | 'droll-to-centre'
  | 'scroll-left' | 'scroll-right' | 'scroll-up' | 'scroll-down';

/**
 * What the number in `DrawPic` meant before SCI1 late.
 *
 * Transcribed from ScummVM's `oldTransitionIDs`, which is the table the
 * interpreter carried.  Four of these were guessed at here before and
 * guessed wrong: 6 and 7 are the diagonal rolls, not the vertical ones,
 * so King's Quest IV's first two pictures -- the Sierra logo and the one
 * behind it -- came in as a pair of closing columns when what the game
 * asked for, and what the game shows, is a square shrinking onto the
 * middle of the screen.  40 to 43 are scrolls, where the old picture is
 * pushed off the edge, not wipes that paint over it.
 */
const OLD_WIPES: Record<number, [Wipe, boolean]> = {
  0: ['vroll-from-centre', false], 1: ['hroll-from-centre', false],
  2: ['straight-from-right', false], 3: ['straight-from-left', false],
  4: ['straight-from-bottom', false], 5: ['straight-from-top', false],
  6: ['droll-to-centre', false], 7: ['droll-from-centre', false],
  8: ['blocks', false],
  9: ['vroll-to-centre', false], 10: ['hroll-to-centre', false],
  11: ['straight-from-right', true], 12: ['straight-from-left', true],
  13: ['straight-from-bottom', true], 14: ['straight-from-top', true],
  15: ['droll-to-centre', true], 16: ['droll-from-centre', true],
  17: ['blocks', true],
  18: ['pixels', false], 27: ['pixels', true],
  30: ['fade', false],
  40: ['scroll-right', false], 41: ['scroll-left', false],
  42: ['scroll-up', false], 43: ['scroll-down', false],
  100: ['none', false],
};

/**
 * What a blacking-out transition runs first, and then in reverse.
 *
 * The styles that carry the flag do the thing twice: once painting
 * black over the picture being left, going the other way, and then
 * again bringing the new one in.  ScummVM's `blackoutTransitionIDs` is
 * where the pairing comes from; everything not named here blacks out
 * with nothing at all.
 */
const BLACKOUT_WIPES: Partial<Record<Wipe, Wipe>> = {
  'vroll-from-centre': 'vroll-to-centre',
  'hroll-from-centre': 'hroll-to-centre',
  'straight-from-right': 'straight-from-left',
  'straight-from-left': 'straight-from-right',
  'straight-from-bottom': 'straight-from-top',
  'straight-from-top': 'straight-from-bottom',
  'droll-from-centre': 'droll-to-centre',
  'droll-to-centre': 'droll-from-centre',
  blocks: 'blocks',
  pixels: 'pixels',
};

/** What SCI0 asked for, as a style and whether to black out first. */
export function wipeFor(animationNr: number): [Wipe, boolean] {
  return OLD_WIPES[animationNr & 0xFF] ?? ['none', false];
}

/** A rectangle the transition is sweeping, as SCI keeps them. */
interface WipeRect { x0: number; y0: number; x1: number; y1: number }

export class Screen {
  /** Palette bytes, so a dither pair survives to the renderer. */
  visual = new Uint8Array(WIDTH * HEIGHT).fill(0xFF);
  priority = new Uint8Array(WIDTH * HEIGHT);
  control = new Uint8Array(WIDTH * HEIGHT);
  /** The picture alone, restored under the cast every frame. */
  private bgVisual = new Uint8Array(WIDTH * HEIGHT).fill(0xFF);
  private bgPriority = new Uint8Array(WIDTH * HEIGHT);
  /** Text above the picture, drawn last and never covered by it. */
  status = '';
  /**
   * The status line's own pixels.
   *
   * It sits outside the picture and survives everything drawn into it,
   * so it gets a plane of its own rather than a corner of the visual
   * one.  White with black text, as SCI0 draws it.
   */
  statusBar = new Uint8Array(WIDTH * STATUS_HEIGHT).fill(0xFF);
  /**
   * Rectangles the picture must not be painted back over.
   *
   * An open window sits above the picture, and the cast is drawn
   * underneath it.  Restoring the whole picture each cycle -- which is
   * this port's shortcut for SCI's per-sprite save and restore --
   * scrubbed any window off the screen the moment anything animated.
   * Camelot's opening menu was drawn and erased inside the same frame,
   * leaving the black backdrop it had been drawn onto.
   */
  windows: Array<{ x0: number; y0: number; x1: number; y1: number }> = [];
  /**
   * Text written straight onto the picture, which must survive too.
   *
   * `Display` draws into the picture rather than into a window of its
   * own -- the intro's narration is written over the scene, once in
   * black and once in white to outline it.  SCI erases only what its
   * sprites covered, so the text stays; restoring the whole picture
   * each cycle wiped it before anyone could read a word.  Cleared when
   * a new picture arrives, which is what would have covered it anyway.
   */
  overlays: Array<{ x0: number; y0: number; x1: number; y1: number; epoch: number }> = [];
  /**
   * Which animation cycle we are in.
   *
   * Narration is written twice in the same cycle -- black, then white
   * over it, which is how the intro outlines its text -- so the pair
   * has to survive together.  What must not survive is the line before
   * it, written in an earlier cycle at the same place.
   */
  epoch = 0;

  /**
   * Put the picture back under text the new text is about to land on.
   *
   * Called before each line is written, so a line replaces the one
   * written where it is going rather than printing on top of it.
   *
   * Only what it lands on.  Clearing every older line instead made the
   * last `Display` call the only one that survived, and Hero's Quest
   * builds its character sheet out of thirty-six of them -- every skill
   * name and every number vanished the moment the next one was written,
   * leaving the player a blank page with two buttons on it.  SCI erases
   * none of this: text is paint on the picture, and what rubs it out is
   * a sprite passing over it or a new room.  Replacing a line in place
   * is the one case the scripts do rely on, and overlapping is what
   * says that is what is happening.
   */
  clearStaleOverlays(rect?: { x0: number; y0: number; x1: number; y1: number }) {
    if (!this.overlays.length) return;
    this.maskStale = true;
    const keep: typeof this.overlays = [];
    for (const o of this.overlays) {
      if (o.epoch === this.epoch) { keep.push(o); continue; }
      if (rect && (o.x0 >= rect.x1 || o.x1 <= rect.x0 || o.y0 >= rect.y1 || o.y1 <= rect.y0)) {
        keep.push(o); continue;
      }
      for (let y = Math.max(0, o.y0); y < Math.min(HEIGHT, o.y1); y++) {
        const row = y * WIDTH;
        for (let x = Math.max(0, o.x0); x < Math.min(WIDTH, o.x1); x++)
          this.visual[row + x] = this.bgVisual[row + x];
      }
    }
    this.overlays = keep;
    this.dirty = true;
  }

  /**
   * Which pixels are spoken for, as a mask.
   *
   * Asked once per pixel of every cel drawn and of every restore, so it
   * cannot be a walk of two lists: with a dialog open nothing animates,
   * the list of written text grows with every cycle, and the cost per
   * pixel grows with it.  That took the game to under a frame a second.
   */
  private mask = new Uint8Array(WIDTH * HEIGHT);
  private maskStale = true;
  /** A window is standing here. */
  private static readonly BY_WINDOW = 1;
  /** Text was written straight onto the picture here. */
  private static readonly BY_OVERLAY = 2;

  /** Say the protected regions have changed. */
  protectionChanged() { this.maskStale = true; }

  /**
   * Windows and written text are kept apart, because they are not owed
   * the same protection.
   *
   * A window is a thing standing in front of the picture and nothing
   * may paint over it while it is open.  Text written by `Display` is
   * not: it is paint on the picture, and SCI lets the cast rub it out
   * -- restoring the background under where a sprite was erases
   * whatever had been written there.  Camelot's purse depends on it.
   * The coin counts are written over the panel, the panel is a view,
   * and closing the purse disposes the view; the counts go because
   * they are inside the rectangle that gets the picture put back.
   * Guarding them from that left three numbers hanging over the room.
   */
  private rebuildMask() {
    this.maskStale = false;
    this.mask.fill(0);
    for (const [list, bit] of [[this.windows, Screen.BY_WINDOW],
                               [this.overlays, Screen.BY_OVERLAY]] as const)
      for (const w of list)
        for (let y = Math.max(0, w.y0); y < Math.min(HEIGHT, w.y1); y++) {
          const row = y * WIDTH;
          for (let x = Math.max(0, w.x0); x < Math.min(WIDTH, w.x1); x++) this.mask[row + x] |= bit;
        }
  }

  private covered(x: number, y: number): boolean {
    if (this.maskStale) this.rebuildMask();
    return this.mask[y * WIDTH + x] !== 0;
  }

  /** Only a window, which is the protection a cast restore must respect. */
  private behindWindow(x: number, y: number): boolean {
    if (this.maskStale) this.rebuildMask();
    return (this.mask[y * WIDTH + x] & Screen.BY_WINDOW) !== 0;
  }

  /** True when nothing is protected, so the fast paths can be taken. */
  private get nothingProtected() { return !this.windows.length && !this.overlays.length; }
  /** Set when the picture changes, so the host knows to repaint. */
  dirty = true;
  /**
   * Blend each dither pair into one colour instead of alternating it.
   *
   * A display choice, not a drawing one: the planes keep the pair byte
   * the hardware wrote, and only `rgb` decides what to make of it.  On
   * by default, because the alternating pattern was a way of faking
   * colours the EGA did not have on a screen that smeared them
   * together, and a modern display shows it as a chequerboard instead.
   */
  undither = true;

  /**
   * The game's own pointer.
   *
   * SCI draws the cursor over everything and never into the picture --
   * it is the hardware's, not the scene's -- so this is composited at
   * render time and the planes never see it.  Baking it in would leave
   * a trail of arrows behind every move.
   */
  cursor: Cursor | null = null;
  cursorVisible = false;
  cursorX = 0;
  cursorY = 0;

  /**
   * Bumped whenever the background changes.
   *
   * Merging a cel's dither pairs is decided against the background it
   * will be drawn over -- a combination is only merged if the picture
   * used it as a dither too -- so a new room means the question has to
   * be asked again.  See `histogram`.
   */
  picEpoch = 0;

  /**
   * Whether the strip above the picture is shown.
   *
   * SCI keeps the status line and the menu bar off screen until they
   * are asked for -- Escape brings the menus down -- and the picture
   * has the whole display to itself until then.  Showing it always left
   * a band across the top that most games never write anything into.
   */
  statusVisible = false;

  /** Rows the display occupies, which the strip changes. */
  get displayHeight() { return HEIGHT + (this.statusVisible ? STATUS_HEIGHT : 0); }

  /**
   * The dither pairs the background uses, cached per picture.
   *
   * A cel's pairs are merged only where the picture merged the same
   * ones, so this is the question every view load has to ask.
   */
  private hist: { epoch: number; counts: Int32Array } | null = null;
  backgroundHistogram(): Int32Array {
    if (this.hist?.epoch !== this.picEpoch)
      this.hist = { epoch: this.picEpoch, counts: histogram(this.bgVisual) };
    return this.hist.counts;
  }

  /**
   * Lay a picture into the background.
   *
   * `reveal` says whether the screen is to show it yet.  SCI keeps the
   * two apart: `DrawPic` composes the picture into the background
   * straight away and raises `picNotValid`, and the screen catches up
   * on the next `Animate`.  That gap matters because the room's `init`
   * runs inside it, and `init` asks the control plane where the ego may
   * stand -- so the planes have to be the new room's even though the
   * screen still shows the old one.
   */
  drawPic(pic: Picture, clear = true, reveal = true) {
    this.picEpoch++;
    // A new picture is a new room: nothing held over from the old one
    // has any business keeping the picture off the screen.  A window a
    // script forgot to dispose would otherwise protect its own stale
    // pixels for the rest of the game -- which is how the intro's
    // narration stayed sitting over Camelot's first room.
    this.overlays.length = 0;
    this.windows.length = 0;
    this.under.length = 0;
    this.maskStale = true;
    if (clear) { this.bgVisual.fill(0xFF); this.bgPriority.fill(0); this.control.fill(0); }
    this.bgVisual.set(pic.visual);
    this.bgPriority.set(pic.priority);
    this.control.set(pic.control);
    if (reveal) this.reveal();
  }

  /** Put the background on the screen, which is what `Animate` does. */
  /**
   * A picture arriving a piece at a time.
   *
   * SCI does this in a loop of its own with the interpreter stopped,
   * copying rectangles of the new screen over the old and sleeping
   * between them; the numbers below are its numbers -- nine
   * milliseconds per thousand pixels dissolved, five per eight blocks,
   * two a column for a sideways wipe, four a row for a vertical one,
   * three and four for the rolls.  Here the loop is spread over frames
   * instead, and the session holds the game still while it runs, which
   * is the same thing seen from the outside.
   */
  private wipe: {
    /** What is running now: the blackout pass, then the real one. */
    style: Wipe; next: Wipe | null;
    began: number; owed: number;
    mask: number; step: number; a: number; done: boolean;
    r: WipeRect[];
  } | null = null;
  /** The screen as it was, shown wherever the new one has not arrived. */
  private wipeFrom = new Uint8Array(WIDTH * HEIGHT);
  /** Which pixels the new picture has reached. */
  private wipeMask = new Uint8Array(WIDTH * HEIGHT);

  /** Is a picture still arriving? */
  get wiping() { return this.wipe !== null; }

  /** Start showing the picture that is already in the background. */
  beginWipe(style: Wipe, blackout: boolean, now: number) {
    if (style === 'none') { this.reveal(); this.wipe = null; return; }
    // The screen as it stands is the one being left, so it is kept
    // before the new picture is put into place, not after.
    this.wipeFrom.set(this.visual);
    this.reveal();
    /**
     * The wipe is put over the picture on its way to the glass, not
     * into the screen the game is drawing on.
     *
     * SCI does it the other way about -- it stops the interpreter and
     * copies the new screen over the old a piece at a time.  Doing
     * that here held the game still for as long as the wipe took, and
     * the intro came apart: the title's numerals were drawn and then
     * painted over, and a credit stayed on the screen for sixty cycles
     * while the sequence caught up.  The game has no business knowing
     * about this, so it does not: it draws as it always did, and what
     * has not been reached yet shows the screen as it was.
     */
    this.wipeMask.fill(0);
    // A blackout runs the paired style first, painting the old picture
    // black as it goes, and the asked-for one after it.
    const first = blackout ? (BLACKOUT_WIPES[style] ?? 'none') : style;
    this.wipe = { style: first, next: blackout ? style : null, began: now,
                  owed: 0, mask: 0x40, step: 0, a: 0, done: false, r: [] };
    if (first === 'none') this.nextPhase();
    else this.setupPhase(first);
    this.advanceWipe(now);
  }

  /** The rectangles a style starts from, as SCI sets them up. */
  private setupPhase(style: Wipe) {
    const w = this.wipe;
    if (!w) return;
    w.style = style; w.owed = 0; w.mask = 0x40; w.step = 0; w.a = 0; w.done = false;
    const mx = WIDTH >> 1, my = HEIGHT >> 1, hh = HEIGHT >> 1;
    const rect = (x0: number, y0: number, x1: number, y1: number) => ({ x0, y0, x1, y1 });
    switch (style) {
      case 'vroll-from-centre':
        w.r = [rect(mx - 1, 0, mx, HEIGHT), rect(mx, 0, mx + 1, HEIGHT)];
        break;
      case 'vroll-to-centre':
        w.r = [rect(0, 0, 1, HEIGHT), rect(WIDTH - 1, 0, WIDTH, HEIGHT)];
        break;
      case 'hroll-from-centre':
        w.r = [rect(0, my - 1, WIDTH, my), rect(0, my, WIDTH, my + 1)];
        break;
      case 'hroll-to-centre':
        w.r = [rect(0, 0, WIDTH, 1), rect(0, HEIGHT - 1, WIDTH, HEIGHT)];
        break;
      case 'droll-from-centre': {
        // Upper, lower, left, right, all four leaving the middle: the
        // square that grows out of the centre of the screen.
        const upper = rect(hh - 2, hh, WIDTH - hh + 1, hh + 1);
        const lower = rect(upper.x0, upper.y0, upper.x1, upper.y1);
        w.r = [upper, lower,
               rect(upper.x0, upper.y0, upper.x0 + 1, lower.y1),
               rect(upper.x1, upper.y0, upper.x1 + 1, lower.y1)];
        break;
      }
      case 'droll-to-centre':
        // And the same four closing on it: the square that shrinks.
        w.r = [rect(0, 0, WIDTH, 1), rect(0, HEIGHT - 1, WIDTH, HEIGHT),
               rect(0, 0, 1, HEIGHT), rect(WIDTH - 1, 0, WIDTH, HEIGHT)];
        break;
      default:
        w.r = [];
    }
  }

  /** The blackout pass is over; bring the new picture in. */
  private nextPhase() {
    const w = this.wipe;
    if (!w) return;
    const style = w.next;
    w.next = null;
    if (!style) { this.wipe = null; this.dirty = true; return; }
    // The pass that has just finished has had its time; the next one
    // starts its own count from there.
    const began = w.began + w.owed;
    this.setupPhase(style);
    w.began = began;
    this.dirty = true;
  }

  /**
   * Say the transition has reached a rectangle.
   *
   * On the blackout pass that means painting the picture being left
   * black; on the real one it means the new picture showing through.
   */
  private wipeRect(x0: number, y0: number, x1: number, y1: number) {
    const blacking = this.wipe?.next != null;
    for (let y = Math.max(0, y0); y < Math.min(HEIGHT, y1); y++) {
      const row = y * WIDTH;
      for (let x = Math.max(0, x0); x < Math.min(WIDTH, x1); x++) {
        if (blacking) this.wipeFrom[row + x] = 0;
        else this.wipeMask[row + x] = 1;
      }
    }
    this.dirty = true;
  }

  private mark(r: WipeRect) { this.wipeRect(r.x0, r.y0, r.x1, r.y1); }

  /**
   * Carry the wipe up to `now`.  Returns true while it is still going.
   */
  advanceWipe(now: number): boolean {
    let guard = 0;
    while (this.wipe && guard++ < 400000) {
      const w = this.wipe;
      if (w.done) { this.nextPhase(); continue; }
      if (w.owed > now - w.began) break;
      this.wipeOnce(w);
    }
    if (!this.wipe) { this.dirty = true; return false; }
    return true;
  }

  /** One unit of work, and what SCI charges for it in milliseconds. */
  private wipeOnce(w: NonNullable<Screen['wipe']>) {
    const [p, q, u, v] = w.r;
    switch (w.style) {
      case 'pixels': {
        // The same shift register SCI uses, so the order is its order.
        for (let i = 0; i < 1024; i++) {
          w.mask = (w.mask & 1) ? (w.mask >> 1) ^ 0xB400 : w.mask >> 1;
          if (w.mask < WIDTH * HEIGHT) {
            const x = w.mask % WIDTH, y = (w.mask / WIDTH) | 0;
            this.wipeRect(x, y, x + 1, y + 1);
          }
          if (w.mask === 0x40) { w.done = true; break; }
        }
        w.owed += 9;
        break;
      }
      case 'blocks': {
        for (let i = 0; i < 8; i++) {
          w.mask = (w.mask & 1) ? (w.mask >> 1) ^ 0x240 : w.mask >> 1;
          if (w.mask < 40 * 25) {
            const x = (w.mask % 40) << 3, y = ((w.mask / 40) | 0) << 3;
            this.wipeRect(x, y, x + 8, y + 8);
          }
          if (w.mask === 0x40) { w.done = true; break; }
        }
        w.owed += 5;
        break;
      }
      case 'straight-from-left':
        this.wipeRect(w.a, 0, w.a + 1, HEIGHT);
        if (++w.a >= WIDTH) w.done = true;
        if ((w.step++ & 1) === 0) w.owed += 2;
        break;
      case 'straight-from-right':
        this.wipeRect(WIDTH - 1 - w.a, 0, WIDTH - w.a, HEIGHT);
        if (++w.a >= WIDTH) w.done = true;
        if ((w.step++ & 1) === 0) w.owed += 2;
        break;
      case 'straight-from-top':
        this.wipeRect(0, w.a, WIDTH, w.a + 1);
        if (++w.a >= HEIGHT) w.done = true;
        w.owed += 4;
        break;
      case 'straight-from-bottom':
        this.wipeRect(0, HEIGHT - 1 - w.a, WIDTH, HEIGHT - w.a);
        if (++w.a >= HEIGHT) w.done = true;
        w.owed += 4;
        break;
      case 'vroll-from-centre': {
        if (p.x0 < 0) { p.x0++; p.x1++; }
        if (q.x1 > WIDTH) { q.x0--; q.x1--; }
        this.mark(p); p.x0--; p.x1--;
        this.mark(q); q.x0++; q.x1++;
        if (p.x1 <= 0 && q.x0 >= WIDTH) w.done = true;
        w.owed += 3;
        break;
      }
      case 'vroll-to-centre': {
        this.mark(p); p.x0++; p.x1++;
        this.mark(q); q.x0--; q.x1--;
        if (p.x0 >= q.x1) w.done = true;
        w.owed += 3;
        break;
      }
      case 'hroll-from-centre': {
        if (p.y0 < 0) { p.y0++; p.y1++; }
        if (q.y1 > HEIGHT) { q.y0--; q.y1--; }
        this.mark(p); p.y0--; p.y1--;
        this.mark(q); q.y0++; q.y1++;
        if (p.y1 <= 0 && q.y0 >= HEIGHT) w.done = true;
        w.owed += 4;
        break;
      }
      case 'hroll-to-centre': {
        this.mark(p); p.y0++; p.y1++;
        this.mark(q); q.y0--; q.y1--;
        if (p.y0 >= q.y1) w.done = true;
        w.owed += 4;
        break;
      }
      case 'droll-from-centre': {
        if (p.y0 < 0) { p.y0++; p.y1++; u.y0++; v.y0++; }
        if (q.y1 > HEIGHT) { q.y0--; q.y1--; u.y1--; v.y1--; }
        if (u.x0 < 0) { u.x0++; u.x1++; p.x0++; q.x0++; }
        if (v.x1 > WIDTH) { v.x0--; v.x1--; p.x1--; q.x1--; }
        this.mark(p); p.y0--; p.y1--; p.x0--; p.x1++;
        this.mark(q); q.y0++; q.y1++; q.x0--; q.x1++;
        this.mark(u); u.x0--; u.x1--; u.y0--; u.y1++;
        this.mark(v); v.x0++; v.x1++; v.y0--; v.y1++;
        if (p.y0 < 0 && q.y1 > HEIGHT) w.done = true;
        w.owed += 4;
        break;
      }
      case 'droll-to-centre': {
        this.mark(p); p.y0++; p.y1++; p.x0++; p.x1--;
        this.mark(q); q.y0--; q.y1--; q.x0++; q.x1--;
        this.mark(u); u.x0++; u.x1++;
        this.mark(v); v.x0--; v.x1--;
        if (p.y0 >= q.y1) w.done = true;
        w.owed += 4;
        break;
      }
      /**
       * A scroll is the only one that moves what is already there.
       *
       * The old picture is pushed off one edge while the new one
       * follows it on, so there is no mask to fill in: how far it has
       * gone is the whole of the state, and the renderer reads both
       * pictures at an offset.  Blacking out first is not a thing any
       * of these do -- ScummVM's table pairs every scroll with nothing.
       */
      case 'scroll-left': case 'scroll-right':
        if (++w.a >= WIDTH) w.done = true;
        if ((w.step++ & 1) === 0) w.owed += 5;
        this.dirty = true;
        break;
      case 'scroll-up': case 'scroll-down':
        if (++w.a >= HEIGHT) w.done = true;
        w.owed += 5;
        this.dirty = true;
        break;
      case 'fade': {
        // SCI fades the palette; with a fixed EGA palette the nearest
        // honest thing is to bring the picture up in even steps.
        const bands = 16;
        for (let y = w.a; y < HEIGHT; y += bands) this.wipeRect(0, y, WIDTH, y + 1);
        if (++w.a >= bands) w.done = true;
        w.owed += 30;
        break;
      }
      default:
        w.done = true;
    }
  }

  reveal() {
    this.restore();
    this.dirty = true;
  }

  /** Put the background back, ready for this frame's cast. */
  /**
   * Rectangles the cast covered last cycle.
   *
   * SCI puts the picture back only where its sprites were, each one
   * saving and restoring the pixels under itself.  This port used to
   * repaint the whole picture instead, which erased everything else
   * drawn on top of it -- a window's own ornament, text written over
   * the scene -- and needed a growing list of exceptions to stop it.
   * Restoring only what was covered removes the problem rather than
   * working around it.
   */
  /** What was on the screen under each cast member, in the order drawn. */
  private under: Array<{ x0: number; y0: number; w: number; h: number;
                        buf: Uint8Array; owner: object | null }> = [];

  /**
   * Put the picture back under whatever the cast covered last cycle.
   *
   * What is protected stays protected.  A sprite is kept from painting
   * over an open window by `blit`, but putting the picture *back*
   * needed the same care and did not have it: wherever a window
   * happened to overlap the rectangle a sprite occupied last cycle,
   * the background was laid straight over the window and ate a strip
   * of it.  Arthur standing beside the parser's message box took the
   * first few letters off it every frame.
   */
  restoreCastAreas(keep: (owner: object | null) => boolean = () => true) {
    this.epoch++;
    this.priority.set(this.bgPriority);
    const guarded = this.windows.length > 0;
    /**
     * Anything a window is standing over is still owed.
     *
     * The window has to be left alone -- Arthur beside the parser's
     * message box took the first few letters off it every frame -- but
     * dropping the saved bits because of that loses them for good, and
     * the sprite's pixels are still sitting there when the window goes.
     * Camelot's parser window left 111 pixels of Arthur behind it on
     * the way out.  So an entry the window covered is carried over and
     * tried again next cycle, and only a cycle that owes nothing clears
     * the list.
     */
    const owed: typeof this.under = [];
    for (let i = this.under.length - 1; i >= 0; i--) {
      const r = this.under[i];
      /**
       * Bits belonging to something that has left the cast are dropped
       * rather than put back.  There is nothing in the list to redraw
       * it, so what it painted becomes part of the scene -- which is
       * how KQ4's "IV" stays on the title after the three pieces fly
       * in, stop and are let go of.
       */
      if (!keep(r.owner)) continue;
      let skipped = false;
      for (let y = 0; y < r.h; y++) {
        const row = (r.y0 + y) * WIDTH;
        for (let x = 0; x < r.w; x++) {
          if (guarded && this.behindWindow(r.x0 + x, r.y0 + y)) { skipped = true; continue; }
          this.visual[row + r.x0 + x] = r.buf[y * r.w + x];
        }
      }
      if (skipped) owed.unshift(r);
    }
    this.under = owed;
    this.dirty = true;
  }

  /**
   * Keep what is under a cel, before it is drawn over it.
   *
   * `owner` is given for a stopped view, whose bits are only owed back
   * while it is still in the cast; an ordinary cel passes null and is
   * always put back.
   */
  castCovered(x0: number, y0: number, x1: number, y1: number, owner: object | null = null) {
    this.under.push({ ...this.save(x0, y0, x1, y1), owner });
  }

  /** Put the picture back over a rectangle now, for scenery coming off. */
  repaintPicture(x0: number, y0: number, x1: number, y1: number) {
    const guarded = this.windows.length > 0;
    for (let y = Math.max(0, y0); y < Math.min(HEIGHT, y1); y++) {
      const row = y * WIDTH;
      for (let x = Math.max(0, x0); x < Math.min(WIDTH, x1); x++) {
        if (guarded && this.behindWindow(x, y)) continue;
        this.visual[row + x] = this.bgVisual[row + x];
      }
    }
    this.dirty = true;
  }

  restore() {
    this.epoch++;
    this.priority.set(this.bgPriority);
    if (this.nothingProtected) { this.visual.set(this.bgVisual); return; }
    if (this.maskStale) this.rebuildMask();
    // Everything but what an open window is showing.
    for (let y = 0; y < HEIGHT; y++) {
      const row = y * WIDTH;
      for (let x = 0; x < WIDTH; x++)
        if (!this.covered(x, y)) this.visual[row + x] = this.bgVisual[row + x];
    }
  }

  /** Bake a cel into the background, as AddToPic does. */
  addToPic(cel: Cel, left: number, top: number, priority: number) {
    this.blit(this.bgVisual, this.bgPriority, cel, left, top, priority, true);
    this.restore();
    this.dirty = true;
  }

  /**
   * Draw a cel over the picture.
   *
   * `writePriority` records the cel's own priority in the plane as it
   * goes, which is what keeps two sprites in the right order where they
   * overlap: without it, whichever is drawn second wins every pixel.
   */
  /**
   * `clip` keeps a cel from painting over an open window.
   *
   * Only the cast asks for that.  A window's own decoration is drawn
   * with this same call, from inside the window, and clipping it there
   * would stop a game drawing the frame it just opened -- which is why
   * Camelot's message panels came up as plain grey boxes with the
   * ornament missing.
   */
  drawCel(cel: Cel, left: number, top: number, priority: number,
          writePriority = false, clip = false) {
    this.blit(this.visual, this.priority, cel, left, top, priority, writePriority, clip);
    this.dirty = true;
  }

  private blit(vis: Uint8Array, pri: Uint8Array, cel: Cel,
               left: number, top: number, priority: number,
               writePriority: boolean, clip = false) {
    for (let y = 0; y < cel.height; y++) {
      const py = top + y;
      if (py < 0 || py >= HEIGHT) continue;
      for (let x = 0; x < cel.width; x++) {
        const px = left + x;
        if (px < 0 || px >= WIDTH) continue;
        const v = cel.pixels[y * cel.width + x];
        if (v === cel.key) continue;
        const i = py * WIDTH + px;
        if (priority < pri[i]) continue;
        // A sprite is behind an open window, never over it.  Written
        // text is a different matter: it is paint on the picture, and
        // a sprite drawn afterwards covers it, as it does in SCI.
        if (clip && this.windows.length && this.behindWindow(px, py)) continue;
        // A cel index is one colour; the pair byte keeps the renderer's
        // two paths identical for pictures and for sprites.
        vis[i] = v < 16 ? ((v << 4) | v) : v;
        if (writePriority) pri[i] = priority;
      }
    }
  }

  /** Draw a string with a decoded font, one glyph at a time. */
  text(font: Font, s: string, x: number, y: number, colour: number): number {
    let cx = x;
    for (const ch of s) {
      const g = font.chars[ch.charCodeAt(0)];
      if (!g) continue;
      for (let gy = 0; gy < g.height; gy++) {
        const py = y + gy;
        if (py < 0 || py >= HEIGHT) continue;
        for (let gx = 0; gx < g.width; gx++) {
          if (!g.bits[gy * g.width + gx]) continue;
          const px = cx + gx;
          if (px < 0 || px >= WIDTH) continue;
          this.visual[py * WIDTH + px] = (colour << 4) | colour;
        }
      }
      cx += g.width;
    }
    this.dirty = true;
    return cx - x;
  }

  /** Copy a rectangle out, so a window can put back what it covered. */
  save(x0: number, y0: number, x1: number, y1: number) {
    /**
     * Clamped at both ends, and the far edge never in front of the
     * near one.
     *
     * A rectangle wholly off the left of the screen arrives with both
     * x's negative; clamping only the near one leaves the far one
     * negative, and a negative end to `subarray` counts back from the
     * end of the screen rather than meaning "empty".  That asks for
     * almost the whole framebuffer and copies it into a buffer with no
     * room, which throws.  KQ4's intro has a cel at -47,-17 a moment
     * after Tamir appears, and the throw stopped the game dead there.
     */
    x0 = Math.max(0, Math.min(WIDTH, x0)); y0 = Math.max(0, Math.min(HEIGHT, y0));
    x1 = Math.max(x0, Math.min(WIDTH, x1)); y1 = Math.max(y0, Math.min(HEIGHT, y1));
    const w = x1 - x0, h = y1 - y0;
    const buf = new Uint8Array(w * h);
    for (let y = 0; y < h; y++)
      buf.set(this.visual.subarray((y0 + y) * WIDTH + x0, (y0 + y) * WIDTH + x1), y * w);
    return { x0, y0, w, h, buf };
  }

  restoreRect(r: { x0: number; y0: number; w: number; h: number; buf: Uint8Array }) {
    for (let y = 0; y < r.h; y++)
      this.visual.set(r.buf.subarray(y * r.w, (y + 1) * r.w), (r.y0 + y) * WIDTH + r.x0);
    this.dirty = true;
  }

  fill(x0: number, y0: number, x1: number, y1: number, colour: number) {
    for (let y = Math.max(0, y0); y < Math.min(HEIGHT, y1); y++)
      for (let x = Math.max(0, x0); x < Math.min(WIDTH, x1); x++)
        this.visual[y * WIDTH + x] = (colour << 4) | colour;
    this.dirty = true;
  }

  /**
   * The pair byte a colour stands for.
   *
   * `Graph` is given the byte the hardware wrote: 31 is the pair 1 and
   * 15, not "colour 31".  Masking it to four bits threw away half of
   * every dithered colour a window drew itself with.
   */
  private pair(c: number): number {
    return c > 15 ? (c & 0xFF) : ((c & 0x0F) << 4) | (c & 0x0F);
  }

  /** A line on the visual plane, for `Graph`'s grDRAW_LINE. */
  line(x0: number, y0: number, x1: number, y1: number, colour: number) {
    const dx = Math.abs(x1 - x0), dy = Math.abs(y1 - y0);
    const sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1;
    let err = dx - dy, x = x0, y = y0;
    const c = this.pair(colour);
    for (let guard = 0; guard < WIDTH + HEIGHT; guard++) {
      this.pxPair(x, y, c);
      if (x === x1 && y === y1) break;
      const e2 = err * 2;
      if (e2 > -dy) { err -= dy; x += sx; }
      if (e2 < dx) { err += dx; y += sy; }
    }
    this.dirty = true;
  }

  /**
   * Fill a rectangle on whichever planes are named.
   *
   * `Graph`'s grFILL_BOX writes to the visual, priority and control
   * planes independently, which is how a window makes room for itself
   * without disturbing what the picture says about depth.
   */
  fillPlanes(x0: number, y0: number, x1: number, y1: number,
             screens: number, visual: number, priority: number, control: number) {
    for (let y = Math.max(0, y0); y < Math.min(HEIGHT, y1); y++) {
      const row = y * WIDTH;
      for (let x = Math.max(0, x0); x < Math.min(WIDTH, x1); x++) {
        if ((screens & 1) && visual >= 0) this.visual[row + x] = this.pair(visual);
        if ((screens & 2) && priority >= 0) this.priority[row + x] = priority & 0x0F;
        if ((screens & 4) && control >= 0) this.control[row + x] = control & 0x0F;
      }
    }
    this.dirty = true;
  }

  frame(x0: number, y0: number, x1: number, y1: number, colour: number) {
    for (let x = x0; x < x1; x++) { this.px(x, y0, colour); this.px(x, y1 - 1, colour); }
    for (let y = y0; y < y1; y++) { this.px(x0, y, colour); this.px(x1 - 1, y, colour); }
  }
  /** One pixel, given a pair byte already. */
  pxPair(x: number, y: number, pair: number) {
    if (x < 0 || x >= WIDTH || y < 0 || y >= HEIGHT) return;
    this.visual[y * WIDTH + x] = pair;
  }

  /** One pixel of the picture, in the pair encoding the planes use. */
  px(x: number, y: number, c: number) {
    if (x < 0 || x >= WIDTH || y < 0 || y >= HEIGHT) return;
    this.visual[y * WIDTH + x] = (c << 4) | c;
  }

  /**
   * RGB for display, with the status line above the picture.
   *
   * Dithered output alternates the pair per pixel the way the hardware
   * did; undithered blends it, which is the same choice the explorer
   * offers on a picture.
   */
  /**
   * Write the status line.
   *
   * The text was being kept and never drawn, which left a black band
   * across the top of every game where the original shows the score.
   */
  drawStatus(font: Font | null, text: string) {
    this.status = text;
    this.statusBar.fill(0xFF);
    if (!font) return;
    let cx = 2;
    const top = Math.max(0, (STATUS_HEIGHT - font.lineHeight) >> 1);
    for (const ch of text) {
      const g = font.chars[ch.charCodeAt(0)];
      if (!g) continue;
      for (let gy = 0; gy < g.height; gy++) {
        const py = top + gy;
        if (py < 0 || py >= STATUS_HEIGHT) continue;
        for (let gx = 0; gx < g.width; gx++) {
          if (!g.bits[gy * g.width + gx]) continue;
          const px = cx + gx;
          if (px < 0 || px >= WIDTH) continue;
          this.statusBar[py * WIDTH + px] = 0x00;
        }
      }
      cx += g.width;
      if (cx >= WIDTH) break;
    }
    this.dirty = true;
  }

  rgb(out = new Uint8Array(WIDTH * this.displayHeight * 3)): Uint8Array {
    const top = this.statusVisible ? STATUS_HEIGHT : 0;
    for (let y = 0; y < top; y++)
      for (let x = 0; x < WIDTH; x++) {
        const v = this.statusBar[y * WIDTH + x];
        const c = this.undither ? BLENDED_RGB[v] : EGA_RGB[ditherPixel(v, x, y)];
        const o = (y * WIDTH + x) * 3;
        out[o] = c[0]; out[o + 1] = c[1]; out[o + 2] = c[2];
      }
    const w = this.wipe;
    /**
     * A scroll shows both pictures at an offset, one leaving and one
     * arriving; everything else shows the new picture where it has
     * reached and the old one where it has not.
     */
    const slide = w && w.style.startsWith('scroll') ? w : null;
    const a = slide?.a ?? 0;
    for (let y = 0; y < HEIGHT; y++) {
      for (let x = 0; x < WIDTH; x++) {
        const i = y * WIDTH + x;
        let v: number;
        if (slide) {
          switch (slide.style) {
            case 'scroll-left':
              v = x < WIDTH - a ? this.wipeFrom[i + a]
                : this.visual[y * WIDTH + x - (WIDTH - a)]; break;
            case 'scroll-right':
              v = x >= a ? this.wipeFrom[i - a]
                : this.visual[y * WIDTH + WIDTH - a + x]; break;
            case 'scroll-up':
              v = y < HEIGHT - a ? this.wipeFrom[(y + a) * WIDTH + x]
                : this.visual[(y - (HEIGHT - a)) * WIDTH + x]; break;
            default:
              v = y >= a ? this.wipeFrom[(y - a) * WIDTH + x]
                : this.visual[(HEIGHT - a + y) * WIDTH + x]; break;
          }
        } else v = !w || this.wipeMask[i] ? this.visual[i] : this.wipeFrom[i];
        const c = this.undither ? BLENDED_RGB[v] : EGA_RGB[ditherPixel(v, x, y)];
        const o = ((y + top) * WIDTH + x) * 3;
        out[o] = c[0]; out[o + 1] = c[1]; out[o + 2] = c[2];
      }
    }
    // Last, and straight into the output: the pointer sits over the
    // status line as readily as over the picture, and belongs to
    // neither.  Its own colours are flat black and white, never a
    // dither pair, so they are written as they are.
    const cur = this.cursor;
    if (cur && this.cursorVisible) {
      const left = this.cursorX - cur.hotspotX;
      const topY = this.cursorY - cur.hotspotY + top;
      const height = this.displayHeight;
      for (let y = 0; y < CURSOR_SIZE; y++) {
        const py = topY + y;
        if (py < 0 || py >= height) continue;
        for (let x = 0; x < CURSOR_SIZE; x++) {
          const p = cur.pixels[y * CURSOR_SIZE + x];
          if (p === CURSOR_CLEAR) continue;
          const px = left + x;
          if (px < 0 || px >= WIDTH) continue;
          const c = EGA_RGB[p & 0x0F];
          const o = (py * WIDTH + px) * 3;
          out[o] = c[0]; out[o + 1] = c[1]; out[o + 2] = c[2];
        }
      }
    }
    return out;
  }
}
