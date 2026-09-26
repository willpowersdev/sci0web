/**
 * A running game: the machine, its screen, and a clock to drive them.
 *
 * The interpreter's main loop never returns, so it cannot be called and
 * waited on.  A session runs it in slices -- one per displayed frame --
 * leaving the frame stack standing between them, which is what turns a
 * program that would block forever into something a browser can host.
 */
import type { Game } from '../resources.ts';
import { Index } from '../script.ts';
import { type Snapshot, PMachine, EV } from './pmachine.ts';
import { WIDTH, SCREEN_HEIGHT } from './screen.ts';

/**
 * What `GameIsRestarting` answers with afterwards.
 *
 * ScummVM's numbering: none is 0, a restart is 1 and a restore is 2.
 * The scripts mostly test it for truth, but `Game::replay` is reached
 * by the restore and not by the restart, so the two are kept apart.
 */
const RESTARTING = 1, RESTORING = 2;

export { WIDTH, SCREEN_HEIGHT };

export interface SessionStatus {
  running: boolean;
  instructions: number;
  frames: number;
  picture: number;
  stopped?: string;
  detail?: string;
}

export class Session {
  vm!: PMachine;
  index: Index;
  /** Instructions per displayed frame; enough for a game cycle, bounded
   *  so one runaway loop cannot freeze the page. */
  budget = 120_000;
  /**
   * Game cycles per second when the game leaves the pace to us.
   *
   * A cycle costs `minWait` ticks, so asking for a rate is asking for
   * the clock to issue that many ticks a second.  Running the clock
   * faster than real time is what makes skipping an intro possible: the
   * game still waits exactly as long as it thinks it does, there is just
   * less of our time in each of its ticks.
   */
  private rate = 20;
  get cyclesPerSecond() { return this.rate; }
  /**
   * Changing the rate rebases the clock's origin.
   *
   * Ticks due are counted from the start of the session at the current
   * rate, so a rate that drops leaves the count already issued far ahead
   * of what the new rate says is due -- and the game's clock then stands
   * still until real time catches up with it.  Coming back to 20 cps
   * after twenty seconds of skipping an intro froze it for ten minutes:
   * `Wait` never returned, so the game never polled, and every key the
   * player pressed queued up unread.  Measuring from here instead keeps
   * the ticks already issued and owes nothing for time spent at the old
   * rate.
   */
  set cyclesPerSecond(v: number) {
    if (v === this.rate) return;
    this.rate = v;
    this.started_at = 0;
    this.ticksIssued = 0;
  }
  /**
   * What one place on the speed control is worth in ticks.
   *
   * The clock's basis, not the game's cycle rate: at the default 20 the
   * clock issues sixty ticks a second, which is real time.  This used to
   * read `this.vm.minWait`, which tied the basis to the cost of a
   * `Wait(0)` -- so answering the games' speed test honestly would have
   * silently slowed every clock in the interpreter by the same factor.
   * The two are separate questions and are now separate numbers.
   */
  private static readonly TICKS_PER_PLACE = 3;
  private get ticksPerSecond() { return this.rate * Session.TICKS_PER_PLACE; }
  instructions = 0;
  frames = 0;
  /**
   * The game's clock runs on wall-clock time, not on displayed frames.
   *
   * An SCI tick is a sixtieth of a second.  Counting one per frame ties
   * the speed of the game to the refresh rate of the screen, so the same
   * game runs twice as fast on a 120 Hz display as on a 60 Hz one.
   */
  private started_at = 0;
  private ticksIssued = 0;
  /**
   * Where the time comes from.
   *
   * A browser paces frames for us, so wall-clock time is the right
   * source there.  A test driving frames in a loop passes no time at
   * all, and a game whose clock never moves waits for ever -- so the
   * source is replaceable, and a harness can hand over a clock it
   * controls.
   */
  now: () => number = () => Date.now();
  private entry: { script: number; pc: number; obj: ReturnType<PMachine['instantiate']> } | null = null;
  private started = false;
  private done: { stopped: string; detail?: string } | null = null;

  private game: Game;

  constructor(game: Game, index?: Index) {
    this.game = game;
    this.index = index ?? new Index(game);
    this.begin();
  }

  /**
   * Build the machine and find where the game starts.
   *
   * `play` for a new game and for a restart; `replay` after a restore,
   * and the difference matters.  ScummVM re-enters the game object at
   * `replay` when a save is loaded and at `play` otherwise, and the
   * scripts are written for it: `Game::play` calls `init`, and
   * `KQ4::init` asks `GameIsRestarting` and, whenever the answer is
   * anything but no, sends the player to room 25.  Coming back through
   * `play` therefore put Rosella on the beach whatever room the save
   * was made in, with everything else about the save correctly
   * restored.  `Game::replay` instead redraws the room the restored
   * globals name and hands control back.
   */
  private begin(entry: string[] = ['play', 'init']) {
    this.vm = new PMachine(this.game, this.index);
    // The wipes are paced off the same clock the session runs on, so a
    // harness driving frames by hand sees them advance too.
    this.vm.wallClock = () => this.now();
    this.vm.putSave = (slot, snap, name) => {
      this.saves.set(slot, { name, snap });
      this.onSave?.();
      return true;
    };
    this.vm.getSave = (slot) => this.saves.get(slot)?.snap ?? null;
    this.vm.listSaves = () => [...this.saves]
      .sort((a, b) => a[0] - b[0])
      .map(([slot, e]) => ({ slot, name: e.name }));
    this.entry = null;
    const obj = this.vm.resolveTarget(null, this.vm.scriptID(0, 0));
    if (!obj) return;
    // Export 0 of script 0 is the game object; `play` is its entry point.
    for (const name of entry) {
      const sel = this.index.selectorId(name);
      if (sel < 0) continue;
      const f = this.vm.species.lookup(obj.def, sel, obj.scriptNo);
      if (!f) continue;
      this.entry = { script: f.script, pc: f.offset, obj: this.vm.instantiate(0, obj.def) };
      break;
    }
  }

  /**
   * Start the game again from script 0, with the flag that says so.
   *
   * A restart in SCI throws the scripts, the clones and the globals
   * away and runs `play` afresh; what it does not throw away is the
   * machinery outside the game, so the picture settings and the chosen
   * output are carried across rather than snapping back to the
   * defaults under the player.  KQ4 reaches its first playable room
   * only this way -- the intro ends by asking for a restart, and
   * `KQ4::init` sends the player to the beach when `GameIsRestarting`
   * says yes.
   */
  private restart(snap: Snapshot | null = null) {
    this.vm.sounds.stopAll();
    const { undither, statusVisible } = this.vm.screen;
    const output = this.vm.sounds.output;
    this.begin(snap ? ['replay', 'play', 'init'] : ['play', 'init']);
    if (snap) this.vm.restoreFrom(snap);
    this.vm.restarting = snap ? RESTORING : RESTARTING;
    this.vm.screen.undither = undither;
    this.vm.screen.statusVisible = statusVisible;
    this.vm.sounds.output = output;
    this.started = false;
    this.started_at = 0;
    this.ticksIssued = 0;
  }

  /**
   * The saved games, which live as long as the session does.
   *
   * SCI hands the slot number and the description to the interpreter
   * and expects it to find somewhere to put them; here that is the
   * host's business, and the page keeps them for the tab.
   */
  saves = new Map<number, { name: string; snap: Snapshot }>();
  /** Told after every save, so a host can put them somewhere. */
  onSave: (() => void) | null = null;

  get ready() { return this.entry !== null; }
  get screen() { return this.vm.screen; }

  /**
   * A key.
   *
   * Repeats are not told apart from presses, which is what ScummVM
   * does: its backend marks a repeat with `kbdRepeat` and the SCI
   * engine never looks at it.  A held key therefore queues at whatever
   * rate the keyboard repeats, and `GetEvent` spends one a cycle.
   */
  key(code: number, modifiers = 0) {
    this.vm.events.push({ type: EV.keyboard, message: code, modifiers,
                          x: this.vm.mouseX, y: this.vm.mouseY });
  }
  /**
   * A press or a release, and which button it was.
   *
   * SCI has no bit for the second button: the mouse interrupt handler
   * reported a right press as an ordinary press with shift held, so
   * that is what the caller passes for one.
   */
  mouse(type: number, x: number, y: number, modifiers = 0) {
    this.vm.mouseX = x; this.vm.mouseY = y;
    this.vm.events.push({ type, message: 0, modifiers, x, y });
  }
  /**
   * Where the pointer is.
   *
   * The screen needs it too, because the cursor is composited at
   * render time rather than drawn into the picture.
   */
  move(x: number, y: number) {
    this.vm.mouseX = x; this.vm.mouseY = y;
    this.screen.cursorX = x; this.screen.cursorY = y;
  }

  /** Run one frame's worth of the game. */
  tick(): SessionStatus {
    if (!this.entry) return { running: false, instructions: 0, frames: 0, picture: -1, stopped: 'no entry point' };
    if (this.done) return { running: false, instructions: this.instructions, frames: this.frames,
                            picture: this.vm.currentPic, ...this.done };
    const now = this.now();
    if (!this.started_at) this.started_at = now;
    // A picture still arriving is shown a piece at a time on its way
    // to the glass; the game itself carries on as though it were there.
    if (this.screen.wiping) this.screen.advanceWipe(now);
    const due = Math.floor((now - this.started_at) * this.ticksPerSecond / 1000);
    if (due > this.ticksIssued) {
      // Cap the catch-up so a page that was in a background tab does not
      // come back and run a minute of game in one frame.  The cap scales
      // with the rate, or asking for speed would be undone by it.
      const cap = Math.max(6, Math.ceil(this.ticksPerSecond / 6));
      this.vm.advanceClock(Math.min(due - this.ticksIssued, cap));
      this.ticksIssued = due;
    }
    const r = this.started
      ? this.vm.run(0, null, 0, { steps: this.budget, resume: true, keep: true, deadline: Date.now() + 120 })
      : this.vm.run(this.entry.script, this.entry.obj, this.entry.pc,
                    { steps: this.budget, keep: true, deadline: Date.now() + 120 });
    // A restart is not the end of the game: the machine is thrown away
    // and built again, and the next tick runs `play` on the new one.
    if (r.stopped === 'restart') {
      const snap = this.vm.restoreRequested;
      this.vm.restoreRequested = null;
      this.restart(snap);
      return { running: true, instructions: this.instructions, frames: this.frames,
               picture: this.vm.currentPic };
    }
    this.started = true;
    this.vm.pumpSounds();
    this.instructions += r.steps;
    this.frames++;
    if (r.stopped !== 'step-limit' && r.stopped !== 'timeout')
      this.done = { stopped: r.stopped, detail: r.detail };
    return { running: !this.done, instructions: this.instructions, frames: this.frames,
             picture: this.vm.currentPic, stopped: this.done?.stopped, detail: this.done?.detail };
  }
}
