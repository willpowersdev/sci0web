/**
 * SCI0 resource explorer.  The engine code is shared with the Node
 * tests; only the byte source and the rendering are browser-specific.
 * No game data ships with this -- the user points it at their own copy.
 */
import { Game, GAME_FILE, TYPE_NAMES, type ResourceSource } from './resources.ts';
import { View, type Cel } from './view.ts';
import { Picture, WIDTH, HEIGHT } from './pic.ts';
import { EGA_RGB, BLENDED_RGB } from './ega.ts';
import { Script, Index, s16 } from './script.ts';
import { sweep, mnemonic } from './disasm.ts';
import { saidDecode, gameGroups, nameTable, stringTable, classTable,
         opcodes, suffixes, parserWords, parserWordsSci01,
         SELECTORS, KERNEL_NAMES, CLASS_TABLE, MAIN_VOCAB, MAIN_VOCAB_SCI01,
         SUFFIX_VOCAB, SUFFIX_VOCAB_SCI01 } from './vocab.ts';
import { strings as textStrings } from './text.ts';
import { Font, Cursor, CURSOR_SIZE, CURSOR_CLEAR } from './font.ts';
import { parseSound, detectHeaderSize, DEVICE_ADLIB } from './sound.ts';
import { Dictation } from './dictation.ts';
import { parseBank, type Instrument } from './opl/patch.ts';
import { Player, resample, TICKS_PER_SECOND } from './opl/player.ts';
import { OPL_RATE } from './opl/opl2.ts';
import { encodeGIF, type Frame } from './gif.ts';
import { encodeWAV } from './wav.ts';
import { Session, SCREEN_HEIGHT } from './vm/session.ts';
import { STATUS_HEIGHT } from './vm/screen.ts';
import { EV, MOD } from './vm/pmachine.ts';
import { Scene } from './scene.ts';
import { picHistogram, unditherCel } from './undither.ts';
import { CrtDisplay } from './crt.ts';
import * as RG from './roomgraph.ts';

const SCALE = 3, ASPECT = 1.2;
/**
 * Elements are looked up by id on every use, so anything that is read
 * back later has to survive the churn.  `#title` is permanent and lives
 * in `#bar`; the viewers rebuild `#controls` instead, because clearing
 * `#bar` would delete `#title` and the next lookup would return null.
 */
const $ = (id: string) => {
  const el = document.getElementById(id);
  if (!el) throw new Error(`missing element #${id}`);
  return el;
};
const cv = $('cv') as HTMLCanvasElement;
const ctx = cv.getContext('2d')!;
const off = document.createElement('canvas');
const octx = off.getContext('2d')!;

let game: Game | null = null;
/** Which game is open, so its saved games are kept apart from another's. */
let gameName = '';
/** Selector and kernel names; built once per game, not per resource. */
let index: Index | null = null;
let groups: Map<number, string[]> | null = null;
/** AdLib instrument bank, read once per game. */
let bank: Instrument[] | null = null;
/** Which room scripts stage each picture, for the sprite overlay. */
let picToScript: Map<number, number[]> | null = null;
/** Pooled dither histogram of every background, built on first use. */
let picHist: Int32Array | null = null;
let showSprites = false;
let viewUndither = false;
let session: Session | null = null;
let raf = 0;
let soundHeader = -1;
let audio: AudioContext | null = null;
let playing: AudioBufferSourceNode | null = null;
/**
 * Where the game's next audio chunk belongs on the output's timeline.
 *
 * The interpreter runs in slices on this thread and a slice is allowed
 * 120ms, so anything rendering audio in step with it would break up.
 * Chunks are rendered ahead instead and scheduled at explicit times, so
 * the sound card plays from a queue and a slow frame is inaudible.
 */
let audioAt = 0;
let gameGain: GainNode | null = null;
/** Seconds of audio kept queued ahead of the output, and chunk size. */
const AUDIO_LEAD = 0.5, AUDIO_CHUNK = 0.1;
let kind = 'pic';
let current: { type: number; num: number } | null = null;
let mode: 'visual' | 'undithered' | 'priority' | 'control' = 'visual';
let anim: number | null = null;
/** Preview frame time; the exported GIF uses the same. */
const ANIM_MS = 140;


/**
 * Where the games are, relative to the page.
 *
 * Relative on purpose.  An absolute `/games/` only works when the app
 * is at the root of its site; written this way it follows the page,
 * so a copy under `example.com/sci/` looks under `sci/games/`.
 */
const GAMES = 'games/';

/**
 * What each folder is actually called.
 *
 * The folders carry ScummVM's short names, because that is what a
 * deployed copy is trimmed into, and the games themselves are no help:
 * the object in script 0 is named ARTHUR, KQ4, CB1, HQ -- abbreviations
 * Sierra used internally, not titles anyone would recognise.  So the
 * list is here, and it covers the SCI0 releases rather than only the
 * ones to hand, since a folder this does not know shows its own name
 * and that is the thing worth avoiding.
 *
 * The name a game is known by, not the one on the box: the subtitle
 * Sierra put after the colon is left off.  Two do not follow that.
 * `iceman`'s colon is inside its name rather than in front of a
 * subtitle, and the two Hoyles are told apart only by their volume,
 * so it stays -- without the colon, to keep the rest of the rule.
 *
 * `qfg1` is named for the box it first came in.  Sierra sold it as
 * Hero's Quest, lost the name to a trademark, and reprinted it as
 * Quest for Glory I; the game object inside still says HQ.
 *
 * `qfg2` is SCI01 rather than SCI0 proper -- the same interpreter a
 * year on -- and is here because this plays it.
 */
const TITLES: Record<string, string> = {
  camelot: 'Conquests of Camelot',
  christmas1988: 'The Sierra Christmas Card',
  hoyle1: 'Hoyle Official Book of Games Volume 1',
  hoyle2: 'Hoyle Official Book of Games Volume 2',
  iceman: 'Codename: ICEMAN',
  kq1sci: "King's Quest",
  kq4sci: "King's Quest IV",
  laurabow: "The Colonel's Bequest",
  lsl2: 'Leisure Suit Larry 2',
  lsl3: 'Leisure Suit Larry 3',
  mothergoose: 'Mixed-Up Mother Goose',
  pq2: 'Police Quest II',
  qfg1: "Hero's Quest",
  qfg2: 'Quest for Glory II',
  sq3: 'Space Quest III',
};

/** The title to show for a folder, or the folder's own name. */
const titleOf = (name: string) => TITLES[name.toLowerCase()] ?? name;

/**
 * What the server has, in one file.
 *
 * A plain web server has no answer for "what is in this directory" --
 * it serves files, not listings -- so a deployment carries a manifest
 * naming each game and its resources.  `npm run manifest` writes one.
 *
 * Read once and kept.  A server that has none is not broken: the
 * directory routes below are asked instead, which is what the
 * development server answers and what a directory index provides.
 */
let manifest: Record<string, string[]> | null | undefined;

async function readManifest(): Promise<Record<string, string[]> | null> {
  if (manifest !== undefined) return manifest;
  manifest = null;
  try {
    const r = await fetch(`${GAMES}games.json`);
    // A missing file can come back as a 404 or as somebody's friendly
    // HTML page, so the parse has to be allowed to fail too.
    if (r.ok) {
      const m = await r.json();
      if (m && typeof m === 'object' && !Array.isArray(m)) manifest = m;
    }
  } catch { /* no manifest; the listing routes still exist */ }
  return manifest ?? null;
}

/**
 * A ResourceSource backed by the server, so the page can be opened
 * directly at a game rather than picking a folder.
 */
async function sourceFromServer(name: string): Promise<ResourceSource> {
  const m = await readManifest();
  const listing: string[] = m?.[name]
    ?? await (await fetch(`${GAMES}${name}/`)).json();
  const want = listing.filter(n => GAME_FILE.test(n));
  if (!want.length) throw new Error(`no SCI0 resources in ${name}`);
  const bytes = new Map<string, Uint8Array>();
  await Promise.all(want.map(async n => {
    const r = await fetch(`${GAMES}${name}/${n}`);
    bytes.set(n, new Uint8Array(await r.arrayBuffer()));
  }));
  return { names: () => [...bytes.keys()], read: (n) => bytes.get(n)! };
}

/**
 * The screen the picture is shown on, when one is asked for.
 *
 * Built on first use and kept: it holds compiled programs and textures,
 * and a browser that will not give us WebGL2 leaves it null for good.
 */
let crt: CrtDisplay | null = null;
let crtTried = false;
/**
 * Whether the game is shown on a tube.
 *
 * On, because it is how the art was meant to be seen.  It is turned off
 * again the moment the browser will not give us WebGL2, and the button
 * that toggles it hides itself in that case.
 */
let enhanced = true;

/**
 * Put a picture on the canvas.
 *
 * `tube` asks for the CRT, and only the game asks: the resource browser
 * is for looking at what is actually in a resource, and scanlines and a
 * phosphor mask across a page of font glyphs or a cursor blown up to
 * fill the screen would be in the way of the one thing that view is
 * for.
 */
function blit(rgb: Uint8Array, w: number, h: number, alpha?: Uint8Array, tube = false) {
  cv.width = w * SCALE; cv.height = Math.round(h * SCALE * ASPECT);
  if (tube && enhanced) {
    if (!crtTried) { crtTried = true; crt = CrtDisplay.create(); }
    if (crt) {
      ctx.imageSmoothingEnabled = false;
      ctx.clearRect(0, 0, cv.width, cv.height);
      ctx.drawImage(crt.render(rgb, w, h, cv.width, cv.height), 0, 0);
      return;
    }
    enhanced = false;                  // no WebGL2; do not ask again
  }
  off.width = w; off.height = h;
  const img = octx.createImageData(w, h);
  for (let i = 0, o = 0; i < w * h; i++) {
    img.data[o++] = rgb[i * 3]; img.data[o++] = rgb[i * 3 + 1];
    img.data[o++] = rgb[i * 3 + 2]; img.data[o++] = alpha ? alpha[i] : 255;
  }
  octx.putImageData(img, 0, 0);
  ctx.imageSmoothingEnabled = false;
  ctx.clearRect(0, 0, cv.width, cv.height);
  ctx.drawImage(off, 0, 0, cv.width, cv.height);
}

function planeRGB(plane: Uint8Array): Uint8Array {
  const out = new Uint8Array(plane.length * 3);
  for (let i = 0, o = 0; i < plane.length; i++) {
    const c = EGA_RGB[plane[i] & 0x0F];
    out[o++] = c[0]; out[o++] = c[1]; out[o++] = c[2];
  }
  return out;
}

function undithered(vis: Uint8Array): Uint8Array {
  const out = new Uint8Array(vis.length * 3);
  for (let i = 0, o = 0; i < vis.length; i++) {
    const c = BLENDED_RGB[vis[i]];
    out[o++] = c[0]; out[o++] = c[1]; out[o++] = c[2];
  }
  return out;
}

function stopAnim() { if (anim !== null) { clearInterval(anim); anim = null; } }

/**
 * Picture number -> every room script that stages it.
 *
 * Built once per game, and only when the sprite overlay is first asked
 * for, since it means parsing every script.  All candidates are kept
 * rather than the lowest-numbered one: several rooms routinely share a
 * background, and the first by number is often the one that places
 * nothing -- QFG2's picture 2 belongs to script 98, which stages no
 * props, and to script 822, which stages fifty-three.
 */
function scriptsForPicture(num: number): number[] {
  if (!picToScript) {
    picToScript = new Map();
    if (index) {
      for (const [scriptNo, room] of RG.collect(game!, index)) {
        if (room.picture === undefined || room.picture === 0 || room.picture === 0xFFFF) continue;
        const l = picToScript.get(room.picture);
        if (l) l.push(scriptNo); else picToScript.set(room.picture, [scriptNo]);
      }
      for (const l of picToScript.values()) l.sort((a, b) => a - b);
    }
  }
  return picToScript.get(num) ?? [];
}

/**
 * The staged room for a picture: the first candidate that places
 * anything.  The rendered buffer is carried along rather than rendered
 * again by the caller, which would cost a second composite for nothing.
 */
interface Staged { rgb: Uint8Array; placed: number; skipped: number; script: number }
function stageFor(num: number, undither: boolean): Staged | null {
  let fallback: Staged | null = null;
  for (const scriptNo of scriptsForPicture(num)) {
    try {
      const scene = new Scene(game!, index!, scriptNo, { undither });
      const rgb = scene.render();
      const got: Staged = { rgb, placed: scene.placed.length,
                            skipped: scene.skipped.length, script: scriptNo };
      if (got.placed) return got;
      fallback ??= got;
    } catch { /* not a room after all */ }
  }
  return fallback;
}

/**
 * How often each dither pair appears across the game's backgrounds.
 *
 * Cel undithering only merges a combination the *backgrounds* also
 * dithered with, which is what stops it eating deliberate chequerboard
 * texture on a sprite.  One picture is not enough evidence -- most games
 * merge nothing at all from a single histogram -- so this pools every
 * pic in the game, once, the first time it is needed.
 */
function backgroundHistogram(): Int32Array {
  if (picHist) return picHist;
  const hist = new Int32Array(256);
  for (const r of game!.byType('pic')) {
    try {
      const h = picHistogram(new Picture(game!.data(1, r.number)));
      for (let i = 0; i < 256; i++) hist[i] += h[i];
    } catch { /* a pic that will not decode contributes nothing */ }
  }
  picHist = hist;
  return hist;
}

/** A button that toggles a flag and redraws. */
function toggle(label: string, on: boolean, title: string, fn: () => void) {
  const b = document.createElement('button');
  b.textContent = label;
  b.title = title;
  if (on) b.style.borderColor = 'var(--accent)';
  b.onclick = fn;
  return b;
}

/**
 * Browser key to the message an SCI0 script expects.
 *
 * Printable keys arrive as their character code.  Everything else is the
 * PC scancode in the high byte, which is the encoding the interpreter
 * handed to scripts and which the games compare against directly.
 */
const SCAN: Record<string, number> = {
  ArrowUp: 0x4800, ArrowDown: 0x5000, ArrowLeft: 0x4B00, ArrowRight: 0x4D00,
  Home: 0x4700, End: 0x4F00, PageUp: 0x4900, PageDown: 0x5100,
  Insert: 0x5200, Delete: 0x5300,
  F1: 0x3B00, F2: 0x3C00, F3: 0x3D00, F4: 0x3E00, F5: 0x3F00,
  F6: 0x4000, F7: 0x4100, F8: 0x4200, F9: 0x4300, F10: 0x4400,
  Enter: 13, Escape: 27, Backspace: 8, Tab: 9, ' ': 32,
};
function keyMessage(e: KeyboardEvent): number | null {
  const s = SCAN[e.key];
  if (s !== undefined) return s;
  if (e.key.length === 1) return e.key.charCodeAt(0);
  return null;
}

/** Stop the game and give the browsing chrome back. */
function stopPlay() {
  if (raf) { cancelAnimationFrame(raf); raf = 0; }
  if (session) session.vm.sounds.stopAll();
  // Chunks already scheduled would otherwise keep playing after the
  // game has gone.
  if (gameGain) { try { gameGain.disconnect(); } catch { /* gone */ } gameGain = null; }
  audioAt = 0;
  session = null;
  document.body.classList.remove('play');
  ($('quit') as HTMLElement).hidden = true;
  ($('hud') as HTMLElement).hidden = true;
  window.removeEventListener('keydown', onPlayKey, true);
  const field = $('dictate') as HTMLInputElement;
  field.removeEventListener('input', onDictate);
  field.removeEventListener('compositionend', onDictate);
  field.blur();
  field.hidden = true;
  clearDictation();
  ($('mic') as HTMLElement).hidden = true;
  ($('speed') as HTMLElement).hidden = true;
  ($('output') as HTMLElement).hidden = true;
  ($('crt') as HTMLElement).hidden = true;
  ($('dither') as HTMLElement).hidden = true;
  cv.removeEventListener('mousedown', grabFocus);
  window.removeEventListener('pointerup', returnFocus);
  window.removeEventListener('focus', grabFocus);
  if (current) render();
}

/**
 * Keys the game needs that are not characters.
 *
 * Printable characters are deliberately left alone here and picked up
 * from the `input` event instead, because that is the only place
 * dictated text appears -- macOS delivers it as an insertion, with no
 * key events at all.  Handling both would type everything twice.
 */
function onPlayKey(e: KeyboardEvent) {
  if (!session) return;
  if (e.key === 'Escape' && e.shiftKey) { stopPlay(); return; }
  // Escape brings the menu strip down, as it does on the original, and
  // takes it away again.  The key still reaches the game.
  if (e.key === 'Escape') session.screen.statusVisible = !session.screen.statusVisible;
  if (e.metaKey) return;                     // leave the browser's own shortcuts alone
  if (e.key.length === 1 && !e.ctrlKey && !e.altKey) return;   // the input event has it
  // Backspace edits the field while there is anything in it, and the
  // deletion is sent from there like any other revision.  Sending it
  // here as well would take back two letters for one press.
  if (e.key === 'Backspace' && dictation.pending !== '') return;
  const m = keyMessage(e);
  if (m === null) return;
  e.preventDefault();
  session.key(m, (e.shiftKey ? MOD.shift : 0) | (e.ctrlKey ? MOD.ctrl : 0)
                 | (e.altKey ? MOD.alt : 0));
  // The game has taken the line.  Leaving the words in the field would
  // make the next thing said look like an edit of the last command.
  if (e.key === 'Enter' || e.key === 'Escape') clearDictation();
}

/**
 * How much of the field the game has already been told about.
 *
 * The field is not emptied as it is read; see `src/dictation.ts` for
 * why, and for what is sent instead.
 */
const dictation = new Dictation();

/** Start the line again, because the game has taken it. */
function clearDictation() {
  const el = $('dictate') as HTMLInputElement | null;
  if (el) el.value = '';
  dictation.reset();
}

/**
 * Text arriving in the hidden field, by typing or by dictation.
 *
 * Only the difference against what was sent last time goes to the game,
 * so a phrase that dictation revises as it hears it arrives once.  Every
 * revision is passed on as it comes, including the ones the browser
 * calls unfinished -- see `src/dictation.ts` for why waiting for it to
 * call them finished means the game hears nothing at all.
 */
function onDictate() {
  const el = $('dictate') as HTMLInputElement;
  const keys = dictation.update(el.value);
  if (session) for (const k of keys) session.key(k);
}

/**
 * Keep the hidden field focused.
 *
 * Only printable characters come through it; everything else is read
 * from a window-level keydown listener.  So losing this focus does not
 * look like "the keyboard stopped working" -- menus, Enter and the
 * arrows all carry on, and only typing goes dead.  Clicking any control
 * in the play bar was enough to do it.
 */
function grabFocus() {
  if (!session) return;
  const el = $('dictate') as HTMLInputElement;
  el.hidden = false;
  clearDictation();
  el.focus({ preventScroll: true });
}

/**
 * Give the keyboard back after the play bar has had its click.
 *
 * A `<select>` needs to keep focus while it is open, so this waits for
 * the end of the event and skips one that is still being used.
 */
function returnFocus(e: Event) {
  const t = e.target as HTMLElement | null;
  if (t && (t.tagName === 'SELECT' || t.tagName === 'OPTION')) return;
  setTimeout(grabFocus, 0);
}

/**
 * Run the game.
 *
 * One slice of interpreter per displayed frame, then the screen is
 * copied to the canvas.  The slice is bounded in both instructions and
 * milliseconds, so a script that never yields slows the game down
 * instead of hanging the tab.
 */
/**
 * Keep the sound card fed from the game's driver.
 *
 * `mix` is pulled for exactly as many samples as the queue is short, so
 * the music is paced by the audio clock rather than by the frame rate
 * and cannot drift away from what the chip is meant to be playing.
 */
/**
 * The synthesiser on the other end of Web MIDI, once one is chosen.
 *
 * The browser only offers this on a secure origin and only after the
 * user has allowed it, so everything here is written to do nothing
 * quietly when there is no port rather than to insist on one.
 */
let midiPort: { send(data: number[]): void } | null = null;
let midiPorts: Array<{ id: string; name: string; port: { send(data: number[]): void } }> = [];

interface MidiLike {
  outputs: Map<string, { id: string; name?: string; send(d: number[]): void }>;
}

/** Ask for the MIDI outputs, and say whether any turned up. */
async function findMidiPorts(): Promise<boolean> {
  const nav = navigator as Navigator & { requestMIDIAccess?: () => Promise<MidiLike> };
  if (!nav.requestMIDIAccess) return false;
  try {
    const access = await nav.requestMIDIAccess();
    midiPorts = [...access.outputs.values()].map(p =>
      ({ id: p.id, name: p.name ?? p.id, port: p }));
    return midiPorts.length > 0;
  } catch { return false; }
}

/**
 * Send whatever the driver has queued.
 *
 * Messages go out as they come due rather than being scheduled ahead:
 * the queue is filled from the game's own clock, which the player can
 * speed up or stop, so a timestamp handed to the synthesiser now may be
 * wrong by the time it arrives.
 */
function pumpMidi(s: Session) {
  const due = s.vm.sounds.takeMidi();
  if (!midiPort) return;
  for (const e of due) {
    const wide = (e.status & 0xF0) !== 0xC0 && (e.status & 0xF0) !== 0xD0;
    midiPort.send(wide ? [e.status, e.a & 0x7F, e.b & 0x7F] : [e.status, e.a & 0x7F]);
  }
}

function pumpAudio(s: Session) {
  const ctx = audio;
  if (!ctx || !gameGain) return;
  const box = s.vm.sounds;
  // A queue that has run dry -- a background tab, a long stall -- is
  // picked up from the present rather than replayed from where it left.
  if (audioAt < ctx.currentTime) audioAt = ctx.currentTime + 0.05;
  const n = Math.round(AUDIO_CHUNK * box.rate);
  const scratch = new Float32Array(n);
  while (audioAt < ctx.currentTime + AUDIO_LEAD) {
    box.mix(scratch);
    const pcm = resample(scratch, box.rate, ctx.sampleRate);
    const buf = ctx.createBuffer(1, pcm.length, ctx.sampleRate);
    buf.copyToChannel(pcm, 0);
    const node = ctx.createBufferSource();
    node.buffer = buf;
    node.connect(gameGain);
    node.start(audioAt);
    audioAt += pcm.length / ctx.sampleRate;
  }
}

/**
 * Saved games, kept in the browser.
 *
 * A cookie was the obvious place and will not do: one holds about four
 * kilobytes and a King's Quest IV save is fourteen, being every global,
 * every script's locals and the clones the game can still reach.
 * `sessionStorage` was the next place and will not do either, for the
 * reason the saves kept disappearing: it lasts exactly as long as the
 * tab, so leaving the game and coming back to it later found nothing.
 * `localStorage` is the same thing without that limit.  Either way
 * nothing is sent anywhere and the server needs nowhere to put it.
 *
 * Each game has its own drawer, because slot 1 means something
 * different in each.
 */
const savesKey = () => `sci0n:saves:${gameName || 'game'}`;

/** Wherever this browser will let us keep them, longest-lived first. */
function drawer(): Storage | null {
  for (const get of [() => localStorage, () => sessionStorage]) {
    try {
      const st = get();
      st.setItem('sci0n:probe', '1');
      st.removeItem('sci0n:probe');
      return st;
    } catch { /* blocked, private mode, or full: try the next */ }
  }
  return null;
}

function keepSaves(s: Session) {
  const text = JSON.stringify([...s.saves]);
  try {
    const st = drawer();
    if (!st) throw new Error('this browser is not storing anything');
    st.setItem(savesKey(), text);
    $('gameinfo').textContent = `${s.saves.size} saved game${s.saves.size === 1 ? '' : 's'} kept in this browser`;
  } catch (err) {
    // Losing it quietly is what made this hard to see: the save worked,
    // restoring worked, and it was gone the moment the game was left.
    console.warn('sci0n: could not keep the saved games', err);
    $('gameinfo').textContent =
      `saved for now, but this browser would not keep it (${Math.round(text.length / 1024)}KB): ${(err as Error).message}`;
  }
}

function loadSaves(s: Session) {
  try {
    const raw = localStorage.getItem(savesKey()) ?? sessionStorage.getItem(savesKey());
    if (!raw) return;
    for (const [slot, entry] of JSON.parse(raw) as Array<[number, { name: string; snap: never }]>)
      s.saves.set(slot, entry);
  } catch {
    // Unreadable or from an older shape: start the drawer empty.
  }
}

function startPlay() {
  if (!game) return;
  stopAnim(); stopSound();
  const s = new Session(game, index ?? undefined);
  if (!s.ready) { $('gameinfo').textContent = 'this game exposes no entry point'; return; }
  session = s;
  (globalThis as { __lastSession?: Session }).__lastSession = s;
  loadSaves(s);
  s.onSave = () => keepSaves(s);
  document.body.classList.add('play');
  stageMode(false);
  ($('quit') as HTMLElement).hidden = false;
  ($('hud') as HTMLElement).hidden = false;
  window.addEventListener('keydown', onPlayKey, true);
  const field = $('dictate') as HTMLInputElement;
  field.addEventListener('input', onDictate);
  // Belt and braces: whatever a composing input event did or did not
  // deliver, the end of the composition is read as well.  Sending the
  // difference twice sends nothing the second time.
  field.addEventListener('compositionend', onDictate);
  ($('mic') as HTMLElement).hidden = false;
  /**
   * How the EGA's dither pairs are shown.
   *
   * The games drew pairs of colours in a chequerboard to fake shades
   * the palette did not have, counting on a monitor that blurred them
   * together.  A modern screen does not, so the pattern is shown rather
   * than the colour it stood for; blending the pair is the default and
   * the toggle puts the original back.
   */
  const dither = $('dither') as HTMLButtonElement;
  dither.hidden = false;
  const showDither = () => {
    dither.textContent = s.screen.undither ? '▦ blended' : '▦ dithered';
  };
  showDither();

  /**
   * The picture on a tube, or flat.
   *
   * On by default, because it is how the art was meant to be seen --
   * the dithered pairs these games are built out of were drawn for a
   * screen that mixes them.  The button puts the flat picture back for
   * anyone who would rather see the pixels, and hides itself where the
   * browser will not give us WebGL2 to draw the tube with.
   */
  const crtBtn = $('crt') as HTMLButtonElement;
  if (!crtTried) { crtTried = true; crt = CrtDisplay.create(); }
  // Nothing to offer, and nothing to turn on, without WebGL2.
  if (!crt) enhanced = false;
  crtBtn.hidden = crt === null;
  const showCrt = () => { crtBtn.textContent = enhanced ? '📺 CRT' : '📺 flat'; };
  showCrt();
  crtBtn.onclick = () => {
    enhanced = !enhanced;
    showCrt();
    if (session) session.screen.dirty = true;
    crtBtn.blur();
    grabFocus();
  };

  dither.onclick = () => {
    if (!session) return;
    session.screen.undither = !session.screen.undither;
    session.screen.dirty = true;
    showDither();
    grabFocus();
  };

  const speed = $('speed') as HTMLSelectElement;
  speed.hidden = false;
  s.cyclesPerSecond = Number(speed.value) || 20;
  speed.onchange = () => {
    if (session) session.cyclesPerSecond = Number(speed.value) || 20;
    // The dropdown keeps the keyboard while it is open; typing has to
    // work again the moment it is done with.
    speed.blur();
    grabFocus();
  };

  /**
   * Where the music goes.
   *
   * The AdLib entry is always there because the game carries its own
   * chip bank; a General MIDI entry appears only once the browser has
   * handed over a synthesiser to send to, and only for a game that
   * ships the MT-32 bank a mapping needs.  Asking for MIDI access
   * prompts the user, so it is asked for when the menu is opened
   * rather than when the game starts.
   */
  const output = $('output') as HTMLSelectElement;
  output.hidden = false;
  const fillOutputs = async () => {
    if (!s.vm.sounds.canPlayGeneralMidi || midiPorts.length) return;
    if (!await findMidiPorts()) return;
    for (const p of midiPorts) {
      const o = document.createElement('option');
      o.value = p.id;
      o.textContent = `GM · ${p.name}`;
      output.append(o);
    }
  };
  output.onpointerdown = () => { void fillOutputs(); };
  output.onchange = () => {
    const chosen = midiPorts.find(p => p.id === output.value);
    midiPort = chosen?.port ?? null;
    s.vm.sounds.setOutput(chosen ? "midi" : "adlib");
    output.blur();
    grabFocus();
  };
  grabFocus();
  // Clicking the picture must not take focus away from the field, and
  // clicking anything else must give it back.
  cv.addEventListener('mousedown', grabFocus);
  window.addEventListener('pointerup', returnFocus);
  // Coming back to the tab should not require a click first.
  window.addEventListener('focus', grabFocus);

  // A page that has not been interacted with may not start audio, so the
  // context is created here and resumed on the first key or click.
  audio ??= new AudioContext();
  gameGain = audio.createGain();
  gameGain.gain.value = 0.8;
  gameGain.connect(audio.destination);
  audioAt = 0;
  void audio.resume();

  // Room for the strip above the picture whether or not it is showing.
  const rgb = new Uint8Array(WIDTH * SCREEN_HEIGHT * 3);
  const frame = () => {
    if (!session) return;
    const st = session.tick();
    const h = session.screen.displayHeight;
    const view = rgb.subarray(0, WIDTH * h * 3);
    session.screen.rgb(view);
    blit(view, WIDTH, h, undefined, true);
    $('hud').textContent =
      `${st.frames} frames · ${(st.instructions / 1e6).toFixed(1)}M instructions` +
      `${st.picture >= 0 ? ` · picture ${st.picture}` : ''}` +
      (session.vm.sounds.active
        ? ` · ♪ ${session.vm.sounds.active}${session.vm.sounds.output === 'midi' ? ' (GM)' : ''}`
        : '') +
      (st.running ? `  ·  ${session.cyclesPerSecond.toFixed(0)} cycles/s` +
                    '  ·  esc for the menu bar  ·  shift-esc to leave  ·  fn fn to dictate'
                  : `  ·  stopped: ${st.stopped ?? ''}`);
    if (session.vm.sounds.output === 'midi') pumpMidi(session);
    else if (session.vm.sounds.available) pumpAudio(session);
    if (st.running) { raf = requestAnimationFrame(frame); return; }
    raf = 0;
    /**
     * The game ended itself.
     *
     * `ret` means its own play loop returned, which is what File >
     * Quit does once its prompt is answered, and what the death screen
     * does when the player declines to carry on.  That is the same
     * ending as pressing Exit, so it leaves the same way -- otherwise
     * the page sat frozen on the last frame in play mode, with no way
     * back to the browser except the keyboard shortcut.
     *
     * A stop for any other reason is a fault, and the last frame and
     * the reason in the bar are the evidence for it; those stay put.
     */
    if (st.stopped === 'ret') stopPlay();
  };
  raf = requestAnimationFrame(frame);
}

/** Hand the browser a file to save, and let go of the object URL after. */
function download(name: string, blob: Blob) {
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a') as HTMLAnchorElement;
  a.href = url; a.download = name;
  a.click();
  setTimeout(() => URL.revokeObjectURL(url), 10_000);
}

/**
 * An export control, styled and labelled so it cannot be mistaken for a
 * view toggle.  "PNG" alone, sitting after four mode buttons, reads as a
 * fifth mode; it needs to say what it does.
 */
function exportButton(label: string, title: string, fn: () => void) {
  const b = document.createElement('button');
  b.className = 'exp';
  b.textContent = `⤓ ${label}`;
  b.title = title;
  b.onclick = fn;
  return b;
}

/** A divider, so the export group reads as separate from what precedes it. */
function separator() {
  const d = document.createElement('div');
  d.className = 'sep';
  return d;
}

/**
 * Save the canvas.
 *
 * It already holds the picture at display scale with the 1.2 aspect
 * correction applied, which is what makes SCI art look right on a
 * square-pixel screen -- so that is what gets written, rather than the
 * raw indexed buffer, and the file matches what is on screen.
 */
function pngButton(name: string) {
  return exportButton('PNG', 'save this image as it appears, at display scale', () => {
    (cv as HTMLCanvasElement).toBlob(blob => { if (blob) download(`${name}.png`, blob); }, 'image/png');
  });
}

/** Save whatever the text pane is currently showing. */
function textButton(name: string) {
  return exportButton('text', 'save this listing as a plain text file', () => {
    const el = $('text');
    const plain = (el.textContent ?? '');
    download(`${name}.txt`, new Blob([plain], { type: 'text/plain;charset=utf-8' }));
  });
}

const esc = (t: string) => t.replace(/[&<>]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]!));
const hex = (n: number, w = 4) => n.toString(16).padStart(w, '0');

/** Swap the stage between the canvas and the text pane. */
function stageMode(text: boolean) {
  // The title artwork is only the opening view; resources and play own the stage after it.
  const cover = document.getElementById('cover');
  if (cover) cover.hidden = true;
  ($('cv') as HTMLElement).hidden = text;
  ($('text') as HTMLElement).hidden = !text;
  $('stage').className = text ? 'text' : '';
}

function showTextPane(html: string) {
  stopAnim();
  stageMode(true);
  $('text').innerHTML = html;
}

/**
 * A text resource is a string table: the game's messages in order.
 * Printing the index alongside each one matters, because that index is
 * what a script's `Print` call refers to.
 */
function showText(num: number) {
  const lines = textStrings(game!.data(3, num));
  // Long messages carry their own newlines; indent the continuations so
  // the index column stays readable.
  const body = lines.map((t, i) => {
    const tag = `<span class="c">${String(i).padStart(3)}</span>  `;
    if (!t) return tag + '<span class="c">·</span>';
    return tag + esc(t).split('\n').join('\n     ');
  }).join('\n');
  showTextPane(`<span class="h">text ${num}</span> <span class="c">· ${lines.length} strings</span>\n\n${body}\n`);
  $('controls').innerHTML = '';
  $('controls').append(separator(), textButton(`text${num}`));
  $('controls').insertAdjacentHTML('beforeend',
    `<span class="dim">text ${num} · ${lines.length} strings · ` +
    `${lines.reduce((a, t) => a + t.length, 0).toLocaleString()} chars</span>`);
}

/**
 * Where each run of code ends.
 *
 * A method's extent is not recorded anywhere -- the script only says
 * where things start.  The next start along is therefore the best
 * available end, which is why every method and export offset has to be
 * collected before any one of them can be disassembled.
 */
function codeBounds(sc: Script): number[] {
  const marks = new Set<number>();
  for (const o of sc.objects) for (const [, off] of o.methods) marks.add(off);
  for (const e of sc.exports) if (e > 0 && e < sc.data.length) marks.add(e);
  for (const [name, off, size] of sc.blocks)
    if (name === 'code') marks.add(off + size);
  marks.add(sc.data.length);
  return [...marks].sort((a, b) => a - b);
}

/**
 * Every glyph in a font, laid out on a grid.
 *
 * Cells are sized to the widest and tallest glyph so the grid stays
 * aligned, and each glyph sits at the cell's top-left -- proportional
 * fonts have glyphs of different widths, and centring them would hide
 * exactly the spacing a font viewer exists to show.
 */
function showFont(num: number) {
  stopAnim();
  stageMode(false);
  const f = new Font(game!.data(7, num));
  const cols = 16;
  const cw = Math.max(1, ...f.chars.map(c => c.width));
  const chh = Math.max(1, ...f.chars.map(c => c.height));
  const rows = Math.max(1, Math.ceil(f.chars.length / cols));
  const w = cols * (cw + 1) + 1, h = rows * (chh + 1) + 1;
  const rgb = new Uint8Array(w * h * 3);
  // A faint grid, so an empty cell is still visibly a cell.
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    if (x % (cw + 1) && y % (chh + 1)) continue;
    const o = (y * w + x) * 3;
    rgb[o] = 32; rgb[o + 1] = 32; rgb[o + 2] = 44;
  }
  f.chars.forEach((c, i) => {
    const ox = (i % cols) * (cw + 1) + 1, oy = Math.floor(i / cols) * (chh + 1) + 1;
    for (let y = 0; y < c.height; y++) for (let x = 0; x < c.width; x++) {
      if (!c.bits[y * c.width + x]) continue;
      const o = ((oy + y) * w + ox + x) * 3;
      rgb[o] = 235; rgb[o + 1] = 235; rgb[o + 2] = 245;
    }
  });
  blit(rgb, w, h);
  $('controls').innerHTML = '';
  $('controls').append(separator(), pngButton(`font${num}`));
  $('controls').insertAdjacentHTML('beforeend',
    `<span class="dim">font ${num} · ${f.chars.length} glyphs · line height ${f.lineHeight}` +
    ` · widest ${cw}px · tallest ${chh}px</span>`);
}

/**
 * A cursor, with its hotspot marked.
 *
 * The hotspot is the pixel the click actually lands on, so it is drawn
 * in as a red cross-hair: without it the image tells you what the cursor
 * looks like but not where it points.
 */
function showCursor(num: number) {
  stopAnim();
  stageMode(false);
  const c = new Cursor(game!.data(8, num));
  const N = CURSOR_SIZE;
  const rgb = new Uint8Array(N * N * 3);
  const alpha = new Uint8Array(N * N);
  for (let i = 0; i < N * N; i++) {
    const v = c.pixels[i];
    if (v === CURSOR_CLEAR) continue;
    const col = EGA_RGB[v & 0x0F];
    rgb[i * 3] = col[0]; rgb[i * 3 + 1] = col[1]; rgb[i * 3 + 2] = col[2];
    alpha[i] = 255;
  }
  // The guide lines only tint pixels the cursor leaves transparent, so
  // marking the hotspot never paints over the art it is describing.
  const hx = c.hotspotX, hy = c.hotspotY;
  if (hx >= 0 && hx < N && hy >= 0 && hy < N) {
    const tint = (i: number, strong: boolean) => {
      if (!strong && alpha[i]) return;
      rgb[i * 3] = 255; rgb[i * 3 + 1] = 40; rgb[i * 3 + 2] = 40;
      alpha[i] = strong ? 255 : 80;
    };
    for (let x = 0; x < N; x++) tint(hy * N + x, false);
    for (let y = 0; y < N; y++) tint(y * N + hx, false);
    tint(hy * N + hx, true);
  }
  blit(rgb, N, N);
  const lit = [...c.pixels].filter(v => v !== CURSOR_CLEAR).length;
  $('controls').innerHTML = '';
  $('controls').append(separator(), pngButton(`cursor${num}`));
  $('controls').insertAdjacentHTML('beforeend',
    `<span class="dim">cursor ${num} · ${N}×${N} · hotspot ${hx},${hy} ` +
    `(marked red) · ${lit} opaque pixels</span>`);
}

function stopSound() {
  if (playing) { try { playing.stop(); } catch { /* already ended */ } playing = null; }
}

/**
 * A sound resource: what it contains, and the AdLib arrangement of it.
 *
 * Rendering runs the whole piece through the OPL2 engine before playing
 * a note of it.  At roughly thirty times real time that costs a moment
 * for a long track, but it keeps the synthesis off the audio thread,
 * where a late buffer is an audible glitch rather than a slow start.
 */
function showSound(num: number) {
  stopAnim();
  stopSound();
  stageMode(true);
  const d = game!.data(4, num);
  const s = parseSound(d, soundHeader >= 0 ? soundHeader : undefined);
  if (!s) {
    showTextPane(`<span class="h">sound ${num}</span> <span class="c">· ${d.length} bytes</span>\n\n` +
      `<span class="c">This is not an SCI0 sound stream.  SCI01 uses a multi-track\n` +
      `header that this decoder does not read.</span>\n`);
    $('controls').innerHTML = '';
    $('controls').insertAdjacentHTML('beforeend', `<span class="dim">sound ${num} · not SCI0</span>`);
    return;
  }
  const notes = s.events.filter(e => (e.status & 0xF0) === 0x90 && e.b > 0).length;
  const used = new Set(s.events.map(e => e.status & 0x0F));
  const out: string[] = [];
  out.push(`<span class="h">sound ${num}</span> <span class="c">· ${s.events.length.toLocaleString()} events · ` +
    `${(s.ticks / TICKS_PER_SECOND).toFixed(1)}s · ${notes.toLocaleString()} notes</span>`);
  out.push('');
  out.push('<span class="k">channels</span>  <span class="c">voices  devices        used</span>');
  for (let i = 0; i < s.channels.length; i++) {
    const c = s.channels[i];
    const dev = c.devices ? '0x' + c.devices.toString(16).padStart(2, '0') : '-';
    out.push(`   ${String(i).padStart(2)}      ${String(c.voices).padStart(5)}   ` +
      `${dev.padEnd(6)} ${(c.devices & DEVICE_ADLIB) ? '<span class="s">AdLib</span>' : '     '}` +
      `   ${used.has(i) ? 'yes' : '<span class="c">no</span>'}`);
  }
  if (s.digital)
    out.push(`\n<span class="k">digital</span>  <span class="c">${s.digital.length.toLocaleString()} bytes of sampled audio follow the music</span>`);
  out.push('');
  out.push('<span class="k">first events</span>');
  for (const e of s.events.slice(0, 24)) {
    const kind = ({ 0x80: 'noteOff', 0x90: 'noteOn', 0xB0: 'control', 0xC0: 'program', 0xE0: 'bend' } as Record<number, string>)[e.status & 0xF0]
      ?? '0x' + (e.status & 0xF0).toString(16);
    out.push(`   <span class="c">${String(e.tick).padStart(6)}</span>  ch ${String(e.status & 0x0F).padStart(2)}  ` +
      `${kind.padEnd(8)} ${String(e.a).padStart(3)} ${String(e.b).padStart(3)}`);
  }
  showTextPane(out.join('\n') + '\n');

  $('controls').innerHTML = '';
  const play = document.createElement('button');
  play.textContent = bank ? 'play' : 'no instrument bank';
  play.onclick = async () => {
    if (!bank) return;
    if (playing) { stopSound(); play.textContent = 'play'; return; }
    play.textContent = 'rendering…';
    audio ??= new AudioContext();
    await audio.resume();
    // Give the button a frame to repaint before the render blocks.
    await new Promise(r => setTimeout(r, 0));
    const p = new Player(s, bank);
    const secs = Math.min(120, p.duration);
    const pcm = resample(p.render(secs), OPL_RATE, audio.sampleRate);
    const b = audio.createBuffer(1, pcm.length, audio.sampleRate);
    b.copyToChannel(pcm, 0);
    const src = audio.createBufferSource();
    src.buffer = b;
    // Normalise to just under full scale.  A fixed gain clips the loud
    // passages of a busy track, which is heard as static rather than as
    // loudness.
    let pk = 0;
    for (const v of pcm) pk = Math.max(pk, Math.abs(v));
    const gain = audio.createGain();
    gain.gain.value = pk > 0 ? Math.min(6, 0.89 / pk) : 1;
    src.connect(gain).connect(audio.destination);
    src.onended = () => { if (playing === src) { playing = null; play.textContent = 'play'; } };
    src.start();
    playing = src;
    play.textContent = 'stop';
  };
  const wav = exportButton('WAV', 'render this tune through the OPL2 and save it', () => {
    if (!bank) return;
    const p = new Player(s, bank);
    const pcm = p.render(Math.min(120, p.duration));
    const out = resample(pcm, OPL_RATE, 44100);
    download(`sound${num}.wav`, new Blob([encodeWAV(out, 44100) as BlobPart], { type: 'audio/wav' }));
  });
  $('controls').append(play, separator(), wav, textButton(`sound${num}`));
  $('controls').insertAdjacentHTML('beforeend',
    `<span class="dim">sound ${num} · ${(s.ticks / TICKS_PER_SECOND).toFixed(1)}s · ` +
    `${notes.toLocaleString()} notes · ${s.channels.length} channels` +
    `${s.digital ? ' · has a digital sample' : ''}</span>`);
}

/** 16 bytes per line, hex and printable gutter. */
function hexDump(d: Uint8Array, limit = 4096): string {
  const rows: string[] = [];
  const n = Math.min(d.length, limit);
  for (let o = 0; o < n; o += 16) {
    const row = d.subarray(o, o + 16);
    const h = Array.from(row, b => b.toString(16).padStart(2, '0')).join(' ').padEnd(47);
    const a = Array.from(row, b => (b >= 32 && b < 127) ? String.fromCharCode(b) : '.').join('');
    rows.push(`<span class="c">${hex(o)}</span>  ${h}  <span class="s">${esc(a)}</span>`);
  }
  if (d.length > n) rows.push(`<span class="c">… ${(d.length - n).toLocaleString()} more bytes</span>`);
  return rows.join('\n');
}

const WORD_CLASS: Array<[number, string]> = [
  [0x001, 'number'], [0x002, 'noun'], [0x004, 'adjective'], [0x008, 'verb'],
  [0x010, 'preposition'], [0x020, 'article'], [0x040, 'pronoun'],
  [0x080, 'conjunction'], [0x100, 'special'],
];
const classBits = (m: number) =>
  WORD_CLASS.filter(([b]) => m & b).map(([, n]) => n).join('|') || `0x${m.toString(16)}`;

/**
 * Vocab resources, each of which is a different format.
 *
 * The number decides the decoder: the word list, the suffix rules, the
 * class table, the selector and kernel name tables and the interpreter's
 * own opcode table all live here under fixed numbers.  Anything without
 * a decoder is shown as bytes rather than guessed at -- a wrong reading
 * presented confidently is worse than an honest hex dump.
 */
function showVocab(num: number) {
  const d = game!.data(6, num);
  const out: string[] = [];
  const head = (what: string, n?: number, unit?: string) =>
    out.push(`<span class="h">vocab ${num}</span> <span class="c">· ${what}` +
             (unit ? ` · ${n!.toLocaleString()} ${unit}` : '') +
             ` · ${d.length.toLocaleString()} bytes</span>`, '');
  let summary = `${d.length.toLocaleString()} bytes`;

  if (num === MAIN_VOCAB || num === MAIN_VOCAB_SCI01) {
    const words = num === MAIN_VOCAB ? parserWords(d) : parserWordsSci01(d);
    head('parser words', words.length, 'words');
    const byGroup = new Map<number, string[]>();
    for (const [w, , grp] of words) {
      const l = byGroup.get(grp); if (l) l.push(w); else byGroup.set(grp, [w]);
    }
    out.push(`<span class="c">${byGroup.size.toLocaleString()} word groups; synonyms share a group</span>`, '');
    for (const [w, cls, grp] of words)
      out.push(`  <span class="s">${esc(w.padEnd(22))}</span>` +
               `<span class="c">group ${String(grp).padStart(5)}  ${esc(classBits(cls))}</span>`);
    summary = `${words.length} words · ${byGroup.size} groups`;

  } else if (num === SUFFIX_VOCAB || num === SUFFIX_VOCAB_SCI01) {
    const suf = suffixes(d);
    if (suf.length >= 4 && suf.every(e => e.pattern)) {
      head('suffix rules', suf.length, 'rules');
      out.push('  <span class="c">pattern            replacement        in       out</span>');
      for (const e of suf)
        out.push(`  <span class="s">${esc(e.pattern.padEnd(18))}${esc(e.replacement.padEnd(18))}</span>` +
                 `<span class="c">0x${e.inClass.toString(16).padStart(4,'0')}   0x${e.outClass.toString(16).padStart(4,'0')}</span>`);
      summary = `${suf.length} suffix rules`;
    } else {
      // SCI01 repurposes 901; without a decoder, show the bytes.
      head('no decoder for this layout');
      out.push(hexDump(d));
    }

  } else if (num === CLASS_TABLE) {
    const t = classTable(d);
    head('class table', t.size, 'species');
    for (const [species, script] of t)
      out.push(`  <span class="c">species</span> ${String(species).padStart(4)}` +
               `  <span class="c">-> script</span> ${String(script).padStart(4)}` +
               `  ${esc(index?.classForSpecies(species)?.name ?? '')}`);
    summary = `${t.size} species`;

  } else if (num === SELECTORS || num === KERNEL_NAMES) {
    const names = nameTable(d);
    head(num === SELECTORS ? 'selector names' : 'kernel names', names.length, 'entries');
    for (let i = 0; i < names.length; i++)
      out.push(`  <span class="c">${String(i).padStart(4)}</span>  <span class="s">${esc(names[i])}</span>`);
    summary = `${names.length} names`;

  } else if (num === 998) {
    const ops = opcodes(d);
    head("the interpreter's own opcode table", ops.length, 'entries');
    for (let i = 0; i < ops.length; i++) {
      const mine = i < 0x40 ? mnemonic(i) : null;
      const agree = i >= 0x40 || ops[i].name === (mine ?? '');
      out.push(`  <span class="c">0x${i.toString(16).padStart(2, '0')}</span>  ` +
               `<span class="s">${esc((ops[i].name || '-').padEnd(12))}</span>` +
               `<span class="c">type ${ops[i].type}${i < 0x40 && !agree ? `  DISAGREES with "${mine}"` : ''}</span>`);
    }
    summary = `${ops.length} opcodes`;

  } else {
    const st = stringTable(d);
    const printable = st.filter(t => t && ![...t].some(c => {
      const v = c.charCodeAt(0); return v < 9 || (v > 13 && v < 32);
    })).length;
    if (st.length && printable >= st.length * 0.6) {
      head('string table (no dedicated decoder)', st.length, 'strings');
      st.forEach((t, i) => { out.push(
        `  <span class="c">${String(i).padStart(4)}</span>  <span class="s">${esc(t)}</span>`); });
      summary = `${st.length} strings`;
    } else {
      head('no decoder for this resource');
      out.push(hexDump(d));
    }
  }

  showTextPane(out.join('\n') + '\n');
  $('controls').innerHTML = '';
  $('controls').append(separator(), textButton(`vocab${num}`));
  $('controls').insertAdjacentHTML('beforeend', `<span class="dim">vocab ${num} · ${summary}</span>`);
}

/** Instructions that push exactly one value and nothing else. */
const FIXED_PUSH = new Set(['push', 'pushi', 'push0', 'push1', 'push2',
                            'pushSelf', 'pprev', 'dup', 'lofss',
                            'pTos', 'ipTos', 'dpTos']);
/** A variable opcode pushes when it loads (l/+/-) to the stack (s). */
const varPushes = (n: string) => n.length >= 2 && n[1] === 's' && 'l+-'.includes(n[0]);
const pushesOne = (n: string) => FIXED_PUSH.has(n) || varPushes(n);
/** Ops with no effect on the value stack, so a scan may step over them. */
const stackNeutral = (n: string) =>
  ['ldi', 'lofsa', 'class', 'lea', 'selfID', 'bnot', 'not', 'neg'].includes(n) ||
  (n.length >= 2 && n[1] === 'a' && 'l+-'.includes(n[0]));
/** The literal a push puts on the stack, or null if it is not a literal. */
function literal(i: { name: string; args: number[] }): number | null {
  if (i.name === 'pushi') return i.args[0];
  if (i.name === 'push0') return 0;
  if (i.name === 'push1') return 1;
  if (i.name === 'push2') return 2;
  return null;
}

/**
 * Which `pushi` instructions are actually selectors.
 *
 * Annotating every `pushi` whose value happens to name a selector is
 * wrong: `pushi 778` is a view number and `pushi 300` an argument, yet
 * both resolve to plausible names.  A send says how many words it takes,
 * so walking back over the pushes that feed it recovers the real
 * (selector, argc, args...) groups.  Anything that makes the walk
 * uncertain -- a pop, a variable-width push, a branch landing in the
 * middle -- abandons that send rather than guessing.
 */
function selectorPushes(ins: Array<{ pc: number; name: string; args: number[] }>): Set<number> {
  const marked = new Set<number>();
  const targets = new Set<number>();
  for (let n = 0; n < ins.length; n++) {
    const i = ins[n];
    if (/^(bt|bnt|jmp)$/.test(i.name) && ins[n + 1])
      targets.add(ins[n + 1].pc + i.args[0]);
  }
  for (let n = 0; n < ins.length; n++) {
    const i = ins[n];
    if (!/^(send|self|super)$/.test(i.name)) continue;
    const words = (i.args[i.args.length - 1] ?? 0) >> 1;
    if (words <= 0) continue;
    const run: number[] = [];
    let k = n - 1;
    for (; k >= 0 && run.length < words; k--) {
      const p = ins[k];
      if (pushesOne(p.name)) run.unshift(k);
      else if (!stackNeutral(p.name)) break;         // a pop, or unknown
      // A branch landing on the first instruction of the run is simply
      // where the run starts; one landing inside it joins two different
      // stack states, so only that case is unsafe.
      if (run.length < words && targets.has(p.pc)) break;
    }
    if (run.length !== words) continue;
    for (let g = 0; g + 1 < run.length;) {
      const sel = literal(ins[run[g]]);
      const argc = literal(ins[run[g + 1]]);
      if (sel === null || argc === null || argc < 0) break;
      if (ins[run[g]].name === 'pushi') marked.add(run[g]);
      g += 2 + argc;
    }
  }
  return marked;
}

function disasmAt(sc: Script, start: number, bounds: number[], idx: Index | null): string {
  const end = bounds.find(b => b > start) ?? sc.data.length;
  const [ins, clean] = sweep(sc.data, start, Math.min(end, sc.data.length));
  const sels = selectorPushes(ins);
  const lines = ins.map((i, n) => {
    // A jump's operand is relative to the *next* instruction, so the
    // following entry's pc is what makes the target readable.
    const after = ins[n + 1]?.pc;
    let note = '';
    if (i.name === 'callk' && idx)
      note = `; ${idx.kernelName(i.args[0])}`;
    else if (/^(bt|bnt|jmp)$/.test(i.name) && after !== undefined)
      note = `; -> ${hex(after + i.args[0])}`;
    else if (/^(lofsa|lofss)$/.test(i.name) && after !== undefined)
      note = `; @${hex(after + i.args[0])}`;
    else if (i.name === 'pushi' && idx && sels.has(n)) {
      const sel = idx.selectorName(i.args[0] << idx.selectorShift);
      if (!sel.startsWith('sel')) note = `; ${sel}`;
    }
    return `      <span class="c">${hex(i.pc)}</span>  ${esc(i.name.padEnd(7))} ` +
           `${esc(i.args.join(', ').padEnd(10))}` +
           (note ? `<span class="c">${esc(note)}</span>` : '');
  });
  if (!clean) lines.push('      <span class="c">… decode stopped early</span>');
  return lines.join('\n');
}

/**
 * The structure of a compiled script: its blocks, its exports, and every
 * object with its properties and disassembled methods.  This is the same
 * view the Node tooling produces, so what the page shows and what the
 * tests compare against stay the same thing.
 */
function showScript(num: number) {
  const sc = new Script(game!.data(2, num), num);
  const idx = index;
  const bounds = codeBounds(sc);
  const out: string[] = [];
  out.push(`<span class="h">script ${num}</span> <span class="c">· ${sc.data.length.toLocaleString()} bytes` +
           `${sc.start ? ' · 2-byte prefix' : ''}</span>`);
  out.push('');
  out.push(`<span class="k">blocks</span>   ` +
    sc.blocks.map(([n, o, sz]) => `${esc(n)}@${hex(o)}+${sz}`).join('  '));
  if (sc.exports.length)
    out.push(`<span class="k">exports</span>  ` +
      sc.exports.map((e, i) => `${i}:${hex(e)}`).join('  '));
  if (sc.locals.length)
    out.push(`<span class="k">locals</span>   ${sc.locals.length} · ` +
      sc.locals.slice(0, 24).map(v => String(s16(v))).join(' ') +
      (sc.locals.length > 24 ? ' …' : ''));

  if (sc.said.length && groups) {
    out.push('');
    out.push(`<span class="k">said</span>`);
    for (const [off, spec] of sc.said)
      out.push(`   <span class="c">${hex(off)}</span>  <span class="s">${esc(saidDecode(spec, groups))}</span>`);
  }
  if (sc.strings.size) {
    out.push('');
    out.push(`<span class="k">strings</span>`);
    for (const [off, t] of sc.strings)
      out.push(`   <span class="c">${hex(off)}</span>  <span class="s">"${esc(t)}"</span>`);
  }

  for (const o of sc.objects) {
    out.push('');
    out.push(`<span class="k">${o.isClass ? 'class' : 'instance'}</span> <b>${esc(o.name)}</b>` +
      ` <span class="c">@${hex(o.offset)} · species ${o.species} · super ${o.superclass}` +
      `${idx && o.species !== null ? ' ' + esc(idx.classForSpecies(o.species)?.name ?? '') : ''}</span>`);
    const names = o.propertyNames(idx);
    out.push(`  <span class="c">properties (${o.propCount})</span>`);
    for (let i = 0; i < o.propCount; i++) {
      const v = o.properties[i];
      out.push(`    ${esc((names[i] ?? `prop${i}`).padEnd(16))}` +
               `${String(s16(v)).padStart(7)}  <span class="c">0x${hex(v)}</span>`);
    }
    if (!o.methods.length) continue;
    out.push(`  <span class="c">methods (${o.methods.length})</span>`);
    for (const [sel, off] of o.methods) {
      out.push(`    <b>${esc(idx ? idx.selectorName(sel) : String(sel))}</b>` +
               ` <span class="c">@${hex(off)}</span>`);
      out.push(disasmAt(sc, off, bounds, idx));
    }
  }
  showTextPane(out.join('\n') + '\n');
  $('controls').innerHTML = '';
  $('controls').append(separator(), textButton(`script${num}`));
  $('controls').insertAdjacentHTML('beforeend',
    `<span class="dim">script ${num} · ${sc.objects.length} objects · ` +
    `${sc.objects.reduce((a, o) => a + o.methods.length, 0)} methods · ` +
    `${sc.exports.length} exports · ${sc.said.length} said</span>`);
}

function showPic(num: number) {
  stopAnim();
  stageMode(false);
  const p = new Picture(game!.data(1, num));
  const flat = mode === 'visual' || mode === 'undithered';
  let rgb: Uint8Array;
  let staged: { placed: number; skipped: number; script: number } | null = null;
  // Sprites only mean anything over the visual planes; priority and
  // control are the data that decides where sprites go, not a picture to
  // put them on.
  const stage = showSprites && flat ? stageFor(num, mode === 'undithered') : null;
  if (stage) {
    rgb = stage.rgb;
    staged = { placed: stage.placed, skipped: stage.skipped, script: stage.script };
  } else {
    rgb = mode === 'priority' ? planeRGB(p.priority)
        : mode === 'control' ? planeRGB(p.control)
        : mode === 'undithered' ? undithered(p.visual)
        : p.visualRGB();
  }
  blit(rgb, WIDTH, HEIGHT);
  $('controls').innerHTML = '';
  for (const m of ['visual', 'undithered', 'priority', 'control'] as const) {
    const b = document.createElement('button');
    b.textContent = m; b.onclick = () => { mode = m; showPic(num); };
    if (m === mode) b.style.borderColor = 'var(--accent)';
    $('controls').append(b);
  }
  if (flat) {
    const rooms = scriptsForPicture(num);
    $('controls').append(toggle('sprites', showSprites,
      rooms.length ? `composite the props staged by script ${rooms.join(' or ')}`
                   : 'no room script stages this picture',
      () => { showSprites = !showSprites; showPic(num); }));
  }
  $('controls').append(separator(), pngButton(`pic${num}_${mode}${staged ? '_scene' : ''}`));
  const bands = p.priorityBands ? ` · bands ${p.priorityBands.join(',')}` : '';
  const note = staged
    ? ` · script ${staged.script}: ${staged.placed} sprites placed` +
      (staged.skipped ? `, ${staged.skipped} skipped` : '')
    : (showSprites && flat ? ' · no room stages this picture' : '');
  $('controls').insertAdjacentHTML('beforeend',
    `<span class="dim">pic ${num} · ${p.ops} opcodes · ${WIDTH}×${HEIGHT}${bands}${note}</span>`);
}

/**
 * Lay a loop's cels out in one frame, aligned by their displacements.
 *
 * Cels in a loop are different sizes and carry their own displacement,
 * so packing each into its own bounding box makes a walk cycle jitter.
 * Placing them the way the engine does -- (x, y) is the bottom centre,
 * displaceX signed and negated when the loop is mirrored, displaceY
 * unsigned -- and taking the union of the results keeps the sprite
 * registered against itself across the whole loop.
 */
function loopFrames(cels: Cel[], delayCs: number):
    { width: number; height: number; frames: Frame[]; key: number } | null {
  if (!cels.length) return null;
  const place = (c: Cel) => {
    const dx = c.mirrored ? -c.xShift : c.xShift;
    const dy = c.yShift >= 0 ? c.yShift : c.yShift + 256;
    const left = dx - (c.width >> 1);
    const bottom = dy + 1;
    return { left, top: bottom - c.height };
  };
  const boxes = cels.map(place);
  const x0 = Math.min(...boxes.map(b => b.left));
  const y0 = Math.min(...boxes.map(b => b.top));
  const x1 = Math.max(...cels.map((c, i) => boxes[i].left + c.width));
  const y1 = Math.max(...cels.map((c, i) => boxes[i].top + c.height));
  const width = Math.max(1, x1 - x0), height = Math.max(1, y1 - y0);
  // One transparent index for the whole file, clear of the 16 colours.
  const key = 16;
  const frames: Frame[] = cels.map((c, i) => {
    const px = new Uint8Array(width * height).fill(key);
    const ox = boxes[i].left - x0, oy = boxes[i].top - y0;
    for (let y = 0; y < c.height; y++) {
      for (let x = 0; x < c.width; x++) {
        const v = c.pixels[y * c.width + x];
        if (v === c.key) continue;
        px[(oy + y) * width + ox + x] = v & 0x0F;
      }
    }
    return { pixels: px, delayCs, transparent: key };
  });
  return { width, height, frames, key };
}

function showView(num: number) {
  stopAnim();
  stageMode(false);
  const v = new View(game!.data(0, num));
  // Undithering rewrites cel pixels in place, so it is applied once to
  // this freshly decoded View rather than on every redraw -- a merged
  // pixel holds a pair byte, and running the detector over its own
  // output again would be reading something it did not produce.
  let merged = 0;
  if (viewUndither) {
    const hist = backgroundHistogram();
    for (const l of v.loops) for (const c of l) merged += unditherCel(c, hist);
  }
  let loop = 0, frame = 0;
  const draw = () => {
    const cels = v.loops[loop] ?? [];
    if (!cels.length) return;
    const c = cels[frame % cels.length];
    const rgb = new Uint8Array(c.width * c.height * 3);
    const alpha = new Uint8Array(c.width * c.height);
    for (let i = 0; i < c.width * c.height; i++) {
      const px = c.pixels[i];
      if (px === c.key) continue;
      // Undithering leaves a colour *pair* behind (>= 0x10), which is
      // blended, while a plain index is one of the sixteen.
      const col = px < 16 ? EGA_RGB[px] : BLENDED_RGB[px];
      rgb[i * 3] = col[0]; rgb[i * 3 + 1] = col[1]; rgb[i * 3 + 2] = col[2];
      alpha[i] = 255;
    }
    blit(rgb, c.width, c.height, alpha);
  };
  $('controls').innerHTML = '';
  const sel = document.createElement('select');
  v.loops.forEach((l, i) => { sel.add(new Option(`loop ${i} (${l.length} cels)`, String(i))); });
  sel.onchange = () => { loop = +sel.value; frame = 0; draw(); };
  const play = document.createElement('button');
  play.textContent = 'play';
  play.onclick = () => {
    if (anim !== null) { stopAnim(); play.textContent = 'play'; return; }
    play.textContent = 'stop';
    anim = window.setInterval(() => { frame++; draw(); }, ANIM_MS);
  };
  const gif = exportButton('GIF', 'save this loop as an animated GIF at native size', () => {
    const cels = v.loops[loop] ?? [];
    const laid = loopFrames(cels, Math.round(ANIM_MS / 10));
    if (!laid) return;
    // 17 entries: the sixteen EGA colours plus one transparent slot.
    const palette = [...EGA_RGB, [0, 0, 0] as [number, number, number]];
    const bytes = encodeGIF({ width: laid.width, height: laid.height,
                              palette, frames: laid.frames });
    download(`view${num}_loop${loop}.gif`,
             new Blob([bytes as BlobPart], { type: 'image/gif' }));
  });
  const und = toggle('undither', viewUndither,
    'merge dither pairs the game\'s backgrounds also use',
    () => { viewUndither = !viewUndither; showView(num); });
  $('controls').append(sel, play, und, pngButton(`view${num}_loop${loop}_cel${frame}`), gif);
  const mnote = viewUndither ? ` · ${merged} combinations merged` : '';
  $('controls').insertAdjacentHTML('beforeend',
    `<span class="dim">view ${num} · ${v.loops.length} loops · ` +
    `mirror 0x${v.mirrorMask.toString(16)}${mnote}</span>`);
  draw();
}

function render() {
  const list = $('list'); list.innerHTML = '';
  if (!game) return;
  const rev = Object.entries(TYPE_NAMES).find(([, n]) => n === kind)?.[0];
  const rows = [...game.resources.values()]
    .filter(r => String(r.type) === rev).sort((a, b) => a.number - b.number);
  for (const r of rows) {
    const d = document.createElement('div');
    d.className = 'row' + (current && current.type === r.type && current.num === r.number ? ' on' : '');
    d.textContent = `${kind} ${r.number}`;
    d.onclick = () => {
      stopSound();
      current = { type: r.type, num: r.number };
      $('title').textContent = `${kind} ${r.number}`;
      try {
        kind === 'pic' ? showPic(r.number)
        : kind === 'view' ? showView(r.number)
        : kind === 'script' ? showScript(r.number)
        : kind === 'text' ? showText(r.number)
        : kind === 'vocab' ? showVocab(r.number)
        : kind === 'font' ? showFont(r.number)
        : kind === 'cursor' ? showCursor(r.number)
        : kind === 'sound' ? showSound(r.number)
        : notVisual();
      }
      catch (e) { $('controls').innerHTML = `<span class="dim">decode failed: ${(e as Error).message}</span>`; }
      render();
    };
    list.append(d);
  }
}

function notVisual() {
  stopAnim();
  stageMode(false);
  $('controls').innerHTML = '<span class="dim">no viewer for this type yet</span>';
  blit(new Uint8Array(WIDTH * HEIGHT * 3), WIDTH, HEIGHT);
}

function buildTabs() {
  const tabs = $('tabs'); tabs.innerHTML = '';
  const present = new Set([...game!.resources.values()].map(r => TYPE_NAMES[r.type]));
  for (const t of ['pic', 'view', 'script', 'text', 'font', 'cursor', 'sound', 'vocab']) {
    if (!present.has(t)) continue;
    const d = document.createElement('div');
    d.className = 'tab' + (t === kind ? ' on' : '');
    d.textContent = t;
    d.onclick = () => { kind = t; buildTabs(); render(); };
    tabs.append(d);
  }
}

/** Describe what was loaded, and show the first tab. */
function adopt(g: Game) {
  game = g;
  index = new Index(g);
  try { groups = gameGroups(g); } catch { groups = null; }
  // The bank and the header size are game-wide facts, so they are read
  // once here rather than per resource -- the header in particular
  // cannot be decided from a single sound (see detectHeaderSize).
  try { bank = parseBank(g.data(9, 3)); } catch { bank = null; }
  picToScript = null; picHist = null;
  try {
    soundHeader = detectHeaderSize([...g.byType('sound')].map(r => g.data(4, r.number)));
  } catch { soundHeader = -1; }
  const counts: Record<string, number> = {};
  for (const r of game.resources.values()) {
    const n = TYPE_NAMES[r.type] ?? String(r.type);
    counts[n] = (counts[n] ?? 0) + 1;
  }
  $('gameinfo').textContent =
    `${game.resources.size} resources · ` +
    Object.entries(counts).sort((a, b) => b[1] - a[1])
      .map(([k, v]) => `${v} ${k}`).join(', ');
  buildTabs(); render();
  ($('play') as HTMLButtonElement).disabled = false;
}

($('quit') as HTMLButtonElement).onclick = stopPlay;
// There is no way to observe the fn key from a page, so the button does
// what it can: it puts the cursor where dictation will land and says so.
($('mic') as HTMLButtonElement).onclick = () => {
  grabFocus();
  const b = $('mic');
  b.classList.add('on');
  b.textContent = '🎤 press fn twice';
  setTimeout(() => { b.classList.remove('on'); b.textContent = '🎤 dictation'; }, 4000);
};
($('play') as HTMLButtonElement).onclick = startPlay;
// The canvas is scaled and aspect-corrected, so a click has to be mapped
// back to the 320x190 the game thinks it is drawing on.
cv.addEventListener('mousemove', (e) => {
  if (!session) return;
  const r = cv.getBoundingClientRect();
  const h = session.screen.displayHeight;
  const x = Math.round((e.clientX - r.left) / r.width * WIDTH);
  const y = Math.round((e.clientY - r.top) / r.height * h) - (h - 190);
  session.move(Math.max(0, Math.min(319, x)), Math.max(-STATUS_HEIGHT, Math.min(189, y)));
});
/**
 * Both halves of a click.
 *
 * A dialog highlights the control under the press and commits it on the
 * release, so sending only the press left Camelot's opening menu
 * following the mouse without ever accepting a choice.
 */
/**
 * The second button belongs to the game, not to the browser.
 *
 * Without this the menu comes up over the picture and the game never
 * sees the click at all.
 */
cv.addEventListener('contextmenu', (e) => { if (session) e.preventDefault(); });

for (const [name, type] of [['mousedown', EV.mouseDown], ['mouseup', EV.mouseUp]] as const) {
  cv.addEventListener(name, (e) => {
    if (!session) return;
    const r = cv.getBoundingClientRect();
    const h = session.screen.displayHeight;
    const x = Math.round(((e as MouseEvent).clientX - r.left) / r.width * WIDTH);
    // The picture starts below the strip only while the strip is shown.
    const y = Math.round(((e as MouseEvent).clientY - r.top) / r.height * h) - (h - 190);
    // A negative y is the strip above the picture, where the menu
    // titles live; clamping it to zero would put every click on the
    // menu bar into the top row of the picture instead.
    // SCI knows the second button only as a press with shift held.
    const mods = (e as MouseEvent).button === 2 ? MOD.right : 0;
    session.mouse(type, Math.max(0, Math.min(319, x)),
                  Math.max(-STATUS_HEIGHT, Math.min(189, y)), mods);
  });
}

/** Load one game from the server and show it. */
async function openGame(name: string) {
  $('gameinfo').textContent = `loading ${titleOf(name)}…`;
  try {
    adopt(new Game(await sourceFromServer(name)));
    gameName = name;
    document.title = `SCI0 Explorer — ${titleOf(name)}`;
    history.replaceState(null, '', `?game=${encodeURIComponent(name)}`);
  } catch (err) {
    $('gameinfo').textContent = `could not load ${titleOf(name)}: ${(err as Error).message}`;
  }
}

/**
 * The games the server has, in a menu that stays put.
 *
 * The sidebar below it belongs to the resource browser as soon as a
 * game is open, so a list of games there could only be the landing
 * page's and vanished the moment it was used.  The menu is in the
 * header and is filled once, whether a game is open or not, so it is
 * the way in and the way between.
 *
 * Returns what it offered, so the caller can say how many there are
 * without asking the server twice.
 */
async function fillGameMenu(): Promise<string[]> {
  const sel = $('games') as HTMLSelectElement | null;
  if (!sel) return [];
  let games: string[] = [];
  const m = await readManifest();
  if (m) games = Object.keys(m).sort();
  else {
    try {
      const r = await fetch(GAMES);
      if (r.ok) games = await r.json();
    } catch { /* opened without a server; the chooser is the way in */ }
  }
  if (!games.length) return games;              // nothing served; stay hidden
  const open = new URLSearchParams(location.search).get('game');
  for (const name of games) {
    const o = document.createElement('option');
    o.value = name;
    o.textContent = titleOf(name);
    if (name === open) o.selected = true;
    sel.append(o);
  }
  sel.hidden = false;
  sel.onchange = () => {
    const name = sel.value;
    if (!name) return;
    // The address bar follows, so the page can be reloaded or shared
    // at whichever game is being looked at.
    history.replaceState(null, '', `?game=${encodeURIComponent(name)}`);
    openGame(name);
  };
  return games;
}

(async () => {
  const q = new URLSearchParams(location.search);
  const name = q.get('game');
  const games = await fillGameMenu();
  if (name) await openGame(name);
  else $('gameinfo').textContent = games.length
    ? `${games.length} games — choose one above`
    : 'no games on this server';
})();
