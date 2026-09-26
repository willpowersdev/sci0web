/**
 * SCI0 PMachine: the execution loop.
 *
 * State is an accumulator, a value stack, and a stack of call frames.
 * Variables come in four flavours -- global (script 0's locals), local
 * (the running script's), temp (allocated on the stack by `link`) and
 * param (pushed by the caller) -- which is why opcodes 0x40-0x7F form a
 * regular block of load/store/inc/dec crossed with those four.
 *
 * A `send` is not always a method call: if the selector names one of the
 * object's properties it is a get (argc 0) or a set (argc 1) instead.
 * Only otherwise does it dispatch through the inheritance chain.
 *
 * Nothing here throws on bad input.  Execution records what went wrong
 * and stops, because a half-ported VM should report its limits rather
 * than pretend.
 */
import type { Game } from '../resources.ts';
import { type Script, type SciObject, Index } from '../script.ts';
import { decode } from '../disasm.ts';
import { SpeciesTable } from './heap.ts';
import { View, type Cel } from '../view.ts';
import { Picture } from '../pic.ts';
import { Font, Cursor } from '../font.ts';
import { strings as textStrings } from '../text.ts';
import { type Wipe, wipeFor, Screen, WIDTH, HEIGHT } from './screen.ts';
import { SoundBox, SIGNAL_FINISHED } from './sounds.ts';
import { MenuBar, SM } from './menu.ts';
import { Parser } from './parser.ts';
import { unditherCel } from '../undither.ts';

/**
 * Debug sampler.  A blocked synchronous loop never reaches a timer or
 * flushes a CPU profile, so the only way to see inside one is to have it
 * report on itself, unbuffered, as it goes.  Off unless SCI_WATCH is set.
 */
const WATCH = typeof process !== 'undefined' && process.env?.SCI_WATCH
  ? Number(process.env.SCI_WATCH) : 0;
let watchTick = 0;
function watch(line: string) {
  if (!WATCH) return;
  if (++watchTick % WATCH) return;
  console.error(line);   // `require` does not exist in an ES module
}

const s16 = (v: number) => (v & 0x8000) ? v - 0x10000 : v;
/**
 * The unsigned comparisons are a distinct opcode for a reason: games use
 * them to test a 16-bit counter against a value written as a negative
 * literal.  Aliasing them to the signed forms makes `GetTime() ugt -1024`
 * -- the idiom that waits out timer wraparound -- true forever.
 */
const u16 = (v: number) => v & 0xFFFF;

/**
 * Object references carry their script.
 *
 * `lofsa` yields a bare offset into the running script, which is fine
 * until the value is stored in a global and sent to from somewhere else
 * -- by then the script it belonged to is lost.  Tagging references with
 * their script keeps them meaningful anywhere, and the tag sits far
 * above the 16-bit range games actually compute with, so ordinary
 * arithmetic is unaffected.
 */
const REF_TAG = 0x40000000;
export const makeRef = (script: number, offset: number) =>
  REF_TAG | ((script & 0x3FFF) << 16) | (offset & 0xFFFF);
export const isRef = (v: number) => (v & REF_TAG) !== 0;
/**
 * Ordering for the unsigned comparisons, where one side may be a pointer.
 *
 * Sierra's own hack, and the scripts are written around it: a number
 * below a certain bound is a number, and anything else is a pointer, so
 * a pointer compared against a small number is the greater of the two.
 * ScummVM puts the bound at 2000 for SCI0 to SCI1.1 and that is the
 * number used here.  Two pointers are ordered by their offsets, which
 * is what comparing within one script means.
 *
 * Making a pointer simply large instead -- big enough to beat anything
 * -- is not the same rule and does not work: SQ3 compares pointers
 * against values well above the bound, and with that version it never
 * got past its title screen.
 */
const ucmp = (a: number, b: number): number => {
  if (isRef(a) !== isRef(b)) {
    const n = (isRef(a) ? b : a) & 0xFFFF;
    if (n <= 2000) return isRef(a) ? 1 : -1;
  }
  const x = a & 0xFFFF, y = b & 0xFFFF;
  return x < y ? -1 : x > y ? 1 : 0;
};
const refScript = (v: number) => (v >> 16) & 0x3FFF;
const refOffset = (v: number) => v & 0xFFFF;

/** Largest temp/param index a frame may address. */
const FRAME_WINDOW = 512;
/** Hard ceiling on the value stack; exceeding it means we have lost track. */
const MAX_STACK = 8192;
/** Frames, not JS stack depth -- an explicit stack can go much deeper. */
const MAX_FRAMES = 1024;
/**
 * Where a `lea` on a temp or a parameter points.
 *
 * SCI's stack is memory like any other, and the scripts do arithmetic
 * on addresses into it.  The saved-game dialog is built on that: the
 * catalogue of names is one buffer of twenty fixed thirty-six byte
 * slots, `DSelector` walks it by adding thirty-six to a pointer until
 * the string it lands on is empty, and `advance` asks for the
 * character *thirty-six past* the cursor to find out whether there is
 * another entry below.  A handle that only stands for one variable
 * answers none of that, so stack addresses get a real address space:
 * script 0x3FFE, with the byte offset of the slot.  Two bytes to the
 * word, exactly as the machine has it, so the script's own `index * 18`
 * words and the kernel's `i * 36` bytes name the same place.
 */
const STACK_SPACE = 0x3FFE;
/**
 * The shape of the saved-game catalogue, which the scripts know too.
 *
 * Twenty is as many as a Sierra dialog will list, thirty-six bytes is
 * the slot each name occupies, and the numbers the scripts are given
 * for the games that exist start at a hundred: anything below that, when
 * it comes back, means "somewhere new", which is how the dialog asks for
 * a save rather than a replacement.  All three are ScummVM's, which took
 * them from the interpreter.
 */
const MAX_SAVES = 20, SAVE_NAME_LEN = 36, SAVE_ID_BASE = 100;
/** The saved game a number from the scripts names. */
const slotOf = (id: number) =>
  id >= SAVE_ID_BASE && id < SAVE_ID_BASE + 100 ? id - SAVE_ID_BASE : id;
const stackAddr = (word: number) => makeRef(STACK_SPACE, word * 2);
const isStackAddr = (v: number) => isRef(v) && refScript(v) === STACK_SPACE;

/**
 * SCI0 event types, as the scripts test them.
 *
 * `peek` is a flag on the mask rather than a type: it asks to look at
 * the queue without taking anything off it.
 */
/**
 * The signal bit that pins an actor's priority.
 *
 * Not a guess: `View::setPri` sets it when given a priority and clears
 * it when given -1, so it is the game's own record of "leave this
 * alone".  Everything without it follows its y down the screen.
 */
/** What `TextSize` wraps at when the caller names no width. */
const TEXT_WIDTH = 192;

/**
 * "I have finished moving; make me part of the scene."
 *
 * A script sets this on a view that has arrived where it belongs.  The
 * interpreter draws it into the picture and turns the bit into
 * `SIGNAL_NO_UPDATE`, after which the view is scenery: the game is free
 * to drop it from the cast, which is what KQ4's title does with the
 * three pieces of its "IV" once they have flown in.  Drawn to the
 * screen instead, as every other cast member is, they lasted until the
 * next thing that repainted from the picture -- the numerals appeared,
 * sat there while the opening question was up, and vanished with it.
 */
export const SIGNAL_STOP_UPDATE = 0x0001;
export const SIGNAL_FIXED_PRIORITY = 0x10;
/**
 * `noTurn`: this object does not face the way it is going.
 *
 * A mover calls `DirLoop` to turn an actor towards its heading, which
 * is right for someone walking and wrong for anything whose loops are
 * not compass directions.  Camelot's intro sails a boat across the
 * water with an animation in loop 0 and the boat itself elsewhere, and
 * `DirLoop` was overwriting the loop the script had chosen.
 */
export const SIGNAL_NO_TURN = 0x800;
/** Set on a client whose step was refused, for the script to read. */
export const SIGNAL_HIT_OBSTACLE = 0x0400;

/**
 * Window styles, as the games pass them to `NewWindow`.
 *
 * A "user" window such as Camelot's options box asks for transparency
 * and draws its own decoration; filling and framing it here paints over
 * what it meant to show.
 */
export const WINDOW_TRANSPARENT = 0x01;
export const WINDOW_NOFRAME = 0x02;
/** `nwNODRAW`: the window is not drawn at all. */
export const WINDOW_NODRAW = 0x08;

/**
 * A control that is a picture rather than words.
 *
 * SCI numbers its controls 1 button, 2 text, 3 edit, 4 icon, 6 list.
 * An icon carries a view, a loop and a cel instead of a string, and
 * Camelot's death and quit box uses one for the little animation that
 * runs beside the question.
 */
export const CONTROL_ICON = 4;
export const CONTROL_LIST = 6;

/**
 * Signal bits that say an actor is not there to be bumped into.
 *
 * 0x4000 is "ignore actors": `Act::canBeHere` skips the whole check when
 * the mover carries it, which is what makes a doorway walkable --
 * Camelot's `door` has it where its `armourStand` and `pouch` do not.
 * The other two cover an actor whose view has been taken away and one
 * the interpreter is not maintaining, neither of which is on the floor
 * to stand on.
 */
export const SIGNAL_NO_BLOCK = 0x4000 | 0x0080 | 0x0004;

export const EV = {
  null: 0x0000, mouseDown: 0x0001, mouseUp: 0x0002,
  // Bit 3 is a key coming back up, not the joystick, which is what it
  // was called here.  SCI1.1 is the first to ask for one, so nothing
  // sends them: an event no game reads would sit in the queue for ever.
  keyboard: 0x0004, keyUp: 0x0008, direction: 0x0040,
  said: 0x0080, peek: 0x8000,
} as const;

/**
 * The modifier bits an event carries, as the games read them.
 *
 * Shift is two bits because the keyboard had two shift keys and the
 * interrupt handler reported which; a script asking "is shift held"
 * tests both.  These are not the browser's numbering and were not the
 * numbering here either -- control and alt were one bit too low, so a
 * script testing for control saw left shift.
 *
 * `right` is the mouse's second button.  SCI has no separate bit for
 * it: the mouse interrupt handler reported a right press as an
 * ordinary press with shift held, and the games' handlers read it that
 * way, so that is what a right click has to look like here.
 */
export const MOD = {
  rightShift: 0x01, leftShift: 0x02, shift: 0x03,
  ctrl: 0x04, alt: 0x08,
  /** The second mouse button, which arrives as a shifted press. */
  right: 0x03,
} as const;

/**
 * Direction keys, as the numeric keypad's scan codes.
 *
 * Directions run clockwise from north, 1 to 8, with 0 for the centre
 * key that stops the ego -- the same numbering the movers use.  The
 * arrow keys send the keypad's codes, which is why there is only one
 * table: on the hardware they were the same keys.
 */
const KEY_DIRECTION: Record<number, number> = {
  0x4700: 8, 0x4800: 1, 0x4900: 2, 0x4B00: 7, 0x4C00: 0,
  0x4D00: 3, 0x4F00: 6, 0x5000: 5, 0x5100: 4,
};

export interface SciEvent {
  type: number; message: number; modifiers: number; x: number; y: number;
}

export class RtObject {
  readonly def: SciObject;
  readonly scriptNo: number;
  /**
   * 32-bit, not 16.  SCI is a 16-bit machine, but this port identifies
   * objects with script-tagged references that do not fit in a word, and
   * properties such as `cycler` and `client` hold exactly those.  Storing
   * them 16-bit silently drops the script tag.  The cost is that
   * arithmetic which relied on 16-bit overflow no longer wraps; the
   * value stack has always behaved that way, so this makes storage
   * consistent with it rather than adding a new deviation.
   */
  props: Int32Array;
  propSelectors: number[];
  constructor(def: SciObject, scriptNo: number, propSelectors: number[]) {
    this.def = def; this.scriptNo = scriptNo;
    // A property the script's relocation list names holds a pointer
    // into that script, and has to arrive as a reference rather than
    // as the bare offset -- the games tell the two apart by size.
    this.props = Int32Array.from(def.properties.map(
      (v, i) => (v && def.isPointer(i)) ? makeRef(scriptNo, v) : s16(v)));
    this.propSelectors = propSelectors;
  }
  /**
   * The value a script sees when it says `self`.
   *
   * It has to be a real reference, not a "this frame's object" sentinel:
   * `(cast add: self)` stores it in a list, and whoever walks that list
   * later has no frame to interpret a sentinel against.  A clone carries
   * its allocated handle here instead of its template's address.
   */
  handle = 0;
  get name() { return this.def.name; }
  indexOfSelector(sel: number) { return this.propSelectors.indexOf(sel); }
}

interface Frame {
  scriptNo: number; obj: RtObject | null; pc: number;
  tempsBase: number; paramsBase: number; argc: number;
  /**
   * A send may carry several (selector, argc, args) groups, and each
   * method among them must finish before the next begins.  With an
   * explicit frame stack the caller cannot simply recurse, so it parks
   * its cursor here and resumes when the callee returns.
   */
  pending?: { target: RtObject; args: number[]; i: number;
              /** `super` resolves from this class, not from the object. */
              fromSpecies?: number };
  /**
   * Calls a kernel function asked for.  `Animate` sends `doit:` to every
   * cast member, but a kernel cannot push frames -- it returns a value to
   * an interpreter that is mid-instruction.  So it parks the queue on the
   * calling frame and the main loop drains it before moving on, with
   * `result` restored to the accumulator once the queue is empty.
   */
  kcalls?: { items: { target: RtObject; sel: number; params: number[] }[];
             i: number; result: number };
}

export interface RunResult {
  steps: number;
  stopped: 'ret' | 'step-limit' | 'timeout' | 'invalid-opcode' | 'unimplemented' | 'error' | 'restart';
  detail?: string;
  kernelCalls: Map<number, number>;
  unresolvedSends: number;
  /** Why sends failed: distinguishes an uninitialised reference from a
   *  bad one, which decides whether more kernel work would even help. */
  unresolvedKind: Map<string, number>;
  maxStack: number;
  maxDepth: number;
  budget?: number;
  deadline?: number;
}

/**
 * Everything a saved game has to put back.
 *
 * ScummVM's `gamestate_restore` resets the engine, reads the segment
 * manager back -- scripts' locals, clones, the object heap -- puts the
 * stack and the clones together again, and then aborts whatever was
 * running and re-enters `play` with `gameIsRestarting` set to restore.
 * The scripts do the rest: `Game::replay` reads the globals it has
 * just been handed and builds the room again.  So what is kept here is
 * the state the scripts own, and nothing about the screen: the room
 * redraws itself.
 */
export interface Snapshot {
  globals: number[];
  locals: Array<[number, number[]]>;
  objects: Array<[string, number[]]>;
  clones: Array<[number, { script: number; offset: number; props: number[] }]>;
  lists: Array<[number, { first: number; last: number }]>;
  nodes: Array<[number, { key: number; value: number; prev: number; next: number }]>;
  strings: Array<[number, string]>;
  nextHandle: number;
  rng: number;
  ticks: number;
  picture: number;
}

export class PMachine {
  game: Game; index: Index; species: SpeciesTable;
  globals = new Int32Array(1024);
  private locals = new Map<number, Int32Array>();
  private scripts = new Map<number, Script>();
  private objects = new Map<string, RtObject>();
  acc = 0;
  prev = 0;
  /**
   * Arguments `&rest` added to the call that follows it.
   *
   * `&rest` does not merely push: it widens the next call.  The compiler
   * emits `pushi sel / push0 / &rest 2 / send 4` for `(send obj sel:
   * &rest)`, where the operand counts only the two words it can see and
   * the rest are added at run time.
   */
  private restAdjust = 0;
  stack: number[] = [];
  frames: Frame[] = [];
  trace: string[] = [];
  traceLimit = 0;
  /** What the game has drawn. */
  screen = new Screen();
  /** Input waiting to be collected by GetEvent. */
  events: SciEvent[] = [];
  /** Where the pointer is, which several kernels report. */
  mouseX = 160;
  mouseY = 95;
  /** Number of the picture currently shown, for the host. */
  currentPic = -1;
  /** The AdLib driver the game drives through `DoSound`. */
  sounds: SoundBox;
  /** The menus a game declares with `AddMenu`. */
  menu = new MenuBar();
  /** The text parser, built from the game's own vocabulary. */
  parser: Parser;

  /**
   * Tell any script waiting on music that its piece has finished.
   *
   * Audio is produced by whatever is pulling samples, which is not the
   * machine, so a finished piece has to be noticed rather than returned.
   * `Sound::check` polls `signal` and a room script's `changeState` will
   * sit on the same state for ever until it reads -1 here.
   */
  pumpSounds() {
    this.sounds.pump(this.ticks);
    /**
     * Cues the music sent, before the news that it finished.
     *
     * A piece marks points in itself -- SCI put them in the stream as
     * program changes on channel 15 -- and a script steps its scene on
     * by polling for them.  Camelot's title sequence is built that way:
     * `credits::doit` watches `titleMusic.prevSignal` for 20, which the
     * piece sends 19.4 seconds in, and only the stopwatch fallbacks ran
     * while these were being dropped.
     */
    for (const { handle, signal } of this.sounds.takeCues()) {
      const obj = this.resolveTarget(null, handle);
      if (obj) this.setProp(obj, 'signal', signal);
    }
    for (const handle of this.sounds.takeEnded()) {
      const obj = this.resolveTarget(null, handle);
      if (obj) this.setProp(obj, 'signal', SIGNAL_FINISHED);
    }
  }
  private fonts = new Map<number, Font | null>();
  private cursors = new Map<number, Cursor | null>();
  private selCache = new Map<string, number>();
  /** Strings the kernel made, which scripts hold by handle. */
  private strings = new Map<number, string>();
  private textRes = new Map<number, string[]>();
  /** Where Display leaves the caret, and what it last drew with. */
  private dsFont = 0;
  /**
   * Ports.  A window makes its own the active one, and everything drawn
   * afterwards is placed relative to it -- which is why a control's tiny
   * `ns` rectangle lands inside the dialog rather than at the top-left
   * of the screen.
   */
  private ports: Array<{ x: number; y: number; w: number; h: number;
                        /** The colours the window was opened with. */
                        pen?: number; back?: number; style?: number }> =
    [{ x: 0, y: 0, w: WIDTH, h: HEIGHT }];
  private windows = new Map<number, {
    /** Null for a window that paints nothing, and so restores nothing. */
    rect: { x0: number; y0: number; w: number; h: number; buf: Uint8Array } | null;
    port: { x: number; y: number; w: number; h: number };
    /** The screen's record of what the picture may not be drawn over. */
    area: { x0: number; y0: number; x1: number; y1: number };
  }>();

  constructor(game: Game, index?: Index) {
    this.game = game;
    this.index = index ?? new Index(game);
    this.sounds = new SoundBox(game, this.index);
    this.parser = new Parser(game);
    this.species = new SpeciesTable(game, this.index);
    const s0 = this.script(0);
    if (s0) this.globals.set(Int32Array.from(s0.locals.map(s16)).subarray(0, 1024));
  }

  /**
   * A script, as the machine should see it.
   *
   * Through the index, which is where the games' own scripts are
   * repaired -- see src/patches.ts.  Reading the resource straight from
   * the game here, as this did, meant nothing in that table ever
   * reached the machine that runs the code: the patches were applied to
   * a copy only the disassembler ever looked at, and the test for them
   * checked the patching and not the running.
   */
  script(n: number): Script | null {
    if (!this.scripts.has(n)) {
      const s = this.index.script(n);
      if (!s) return null;
      this.scripts.set(n, s);
      // Locals get the same relocation treatment as properties: a word
      // the script names as a pointer is a reference, not a number.
      this.locals.set(n, Int32Array.from(s.locals.map((v, i) =>
        (v && s.localsAt >= 0 && s.relocations.has(s.localsAt + i * 2))
          ? makeRef(n, v) : s16(v))));
    }
    return this.scripts.get(n) ?? null;
  }

  localsOf(n: number): Int32Array {
    if (!this.locals.has(n)) this.script(n);
    return this.locals.get(n) ?? new Int32Array(0);
  }

  /**
   * Every clone the game can still reach, from the roots outwards.
   *
   * SCI frees a disposed clone at the next garbage collection, and
   * collection is by reachability: what nothing holds a reference to is
   * gone whether it was disposed or not.  Here collection happens when
   * a cycle begins, which is never while a modal dialog is up -- the
   * dialog polls `GetEvent` in a loop, cloning an `Event` each time
   * round, and the machine suspends and resumes that one cycle rather
   * than starting another.  A saved game made in the save dialog
   * therefore carried a hundred and fifty thousand dead events: thirteen
   * megabytes, three times what a browser will store, so the save was
   * written nowhere, silently, and was gone as soon as the game was
   * left.  What is still reachable is seventy.
   *
   * The roots are the globals, every script's locals, the value stack --
   * which is where a suspended cycle keeps the event it is working on --
   * and the properties of everything already reached.
   */
  private reachableClones(): Set<number> {
    const seen = new Set<number>();
    const queue: number[] = [];
    // Nothing recurses: a node chain is as long as the list it belongs
    // to, and a list of a hundred and fifty thousand dead events walked
    // by recursion is a stack overflow, which stopped the game dead in
    // the middle of saving.  Lists and nodes are all roots anyway --
    // every one of them is kept by the save -- so reaching a clone
    // through one needs no walk of its own.
    const visit = (v: number) => {
      if (!isRef(v) || seen.has(v) || !this.clones.has(v)) return;
      seen.add(v); queue.push(v);
    };
    for (const v of this.globals) visit(v);
    for (const v of this.stack) visit(v);
    for (const ls of this.locals.values()) for (const v of ls) visit(v);
    for (const o of this.objects.values()) for (const v of o.props) visit(v);
    for (const l of this.lists.values()) { visit(l.first); visit(l.last); }
    for (const n of this.nodes.values()) { visit(n.key); visit(n.value); visit(n.prev); visit(n.next); }
    while (queue.length) {
      const o = this.clones.get(queue.pop()!);
      if (o) for (const v of o.props) visit(v);
    }
    return seen;
  }

  /** The state a saved game keeps, as ScummVM's serialiser keeps it. */
  snapshot(): Snapshot {
    const reachable = this.reachableClones();
    return {
      globals: Array.from(this.globals),
      locals: [...this.locals].map(([n, v]) => [n, Array.from(v)] as [number, number[]]),
      objects: [...this.objects].map(([k, o]) => [k, Array.from(o.props)] as [string, number[]]),
      // Only the clones the game can still get at.  A save made from
      // inside a dialog is otherwise mostly the dialog's own discarded
      // events -- see `reachable`.
      clones: [...this.clones]
        .filter(([h]) => reachable.has(h))
        .map(([h, o]) =>
          [h, { script: o.scriptNo, offset: o.def.offset, props: Array.from(o.props) }] as
            [number, { script: number; offset: number; props: number[] }]),
      lists: [...this.lists].map(([h, l]) => [h, { ...l }] as [number, { first: number; last: number }]),
      nodes: [...this.nodes].map(([h, n]) => [h, { ...n }] as
        [number, { key: number; value: number; prev: number; next: number }]),
      strings: [...this.strings],
      nextHandle: this.nextHandle,
      rng: this.rng,
      ticks: this.ticks,
      picture: this.currentPic,
    };
  }

  /**
   * Put a saved game back.
   *
   * Called on a machine built fresh, so everything the scripts own is
   * simply written over what a new game had.
   */
  restoreFrom(snap: Snapshot) {
    this.globals.fill(0);
    for (let i = 0; i < snap.globals.length && i < this.globals.length; i++)
      this.globals[i] = snap.globals[i];
    this.locals.clear();
    for (const [n, v] of snap.locals) this.locals.set(n, Int32Array.from(v));
    for (const [key, props] of snap.objects) {
      const cut = key.indexOf(':');
      const scriptNo = Number(key.slice(0, cut)), offset = Number(key.slice(cut + 1));
      const def = this.script(scriptNo)?.objects.find(d => d.offset === offset);
      if (!def) continue;
      const o = this.instantiate(scriptNo, def);
      for (let i = 0; i < props.length && i < o.props.length; i++) o.props[i] = props[i];
    }
    this.clones.clear();
    for (const [h, c] of snap.clones) {
      const def = this.script(c.script)?.objects.find(d => d.offset === c.offset);
      if (!def) continue;
      const sels = def.propSelectors ?? this.species.classOf(def.species)?.propSelectors ?? [];
      const o = new RtObject(def, c.script, sels);
      o.handle = h;
      for (let i = 0; i < c.props.length && i < o.props.length; i++) o.props[i] = c.props[i];
      this.clones.set(h, o);
    }
    this.lists.clear();
    for (const [h, l] of snap.lists) this.lists.set(h, { ...l });
    this.nodes.clear();
    for (const [h, n] of snap.nodes) this.nodes.set(h, { ...n });
    this.strings.clear();
    for (const [h, t] of snap.strings) this.strings.set(h, t);
    this.nextHandle = snap.nextHandle;
    this.rng = snap.rng;
    this.ticks = snap.ticks;
  }

  /** Where a saved game is kept, which is the host's business. */
  putSave: ((slot: number, snap: Snapshot, name: string) => boolean) | null = null;
  getSave: ((slot: number) => Snapshot | null) | null = null;
  /** What is in the drawer, oldest slot first, for the game's own dialog. */
  listSaves: (() => Array<{ slot: number; name: string }>) | null = null;
  /** The save directory the scripts pass around; one string, reused. */
  private saveDir = 0;

  /**
   * Which slot a save should go to.
   *
   * A number in the official range names a game that already exists and
   * is being replaced; anything below it means the dialog wants a slot
   * of its own, and the lowest free one is it.  Sierra's dialog passes
   * the number of games it found, so without this every save after the
   * first overwrote the one before.
   */
  private slotToWrite(id: number): number {
    const taken = new Set((this.listSaves?.() ?? []).map(e => e.slot));
    if (id >= SAVE_ID_BASE && id < SAVE_ID_BASE + 100) {
      const slot = id - SAVE_ID_BASE;
      return taken.has(slot) ? slot : -1;
    }
    let slot = 0;
    while (taken.has(slot)) slot++;
    return slot;
  }
  /** A restore waiting for the machine to be built again. */
  restoreRequested: Snapshot | null = null;

  /** Scripts asked to unload while they were still running. */
  private unloadPending = new Set<number>();

  /**
   * Forget a script's objects and locals, so the next use rebuilds
   * them from the resource with the values it was compiled with.
   */
  private unloadScript(n: number) {
    const prefix = `${n}:`;
    for (const key of [...this.objects.keys()])
      if (key.startsWith(prefix)) this.objects.delete(key);
    // The parsed script goes too, because that is what seeds the
    // locals: dropping the locals alone leaves `script` believing it
    // has already done the work, and the next load finds none.  KQ4's
    // water region keeps the last ground it saw in local 1, so with no
    // locals at all the read fell out of range, the comparison saw the
    // accumulator it had just put there, and the region decided the
    // ground had not changed -- every cycle, for ever.
    this.locals.delete(n);
    this.scripts.delete(n);
  }

  /** Runtime instance of a static object, with its own mutable properties. */
  instantiate(scriptNo: number, def: SciObject): RtObject {
    const key = `${scriptNo}:${def.offset}`;
    let o = this.objects.get(key);
    if (!o) {
      const sels = def.propSelectors ??
        this.species.classOf(def.species)?.propSelectors ?? [];
      o = new RtObject(def, scriptNo, sels);
      o.handle = makeRef(scriptNo, def.offset + 12);
      this.objects.set(key, o);
    }
    return o;
  }

  /** Object whose property array begins at `ptr` (SCI0: block + 12). */
  objectAt(scriptNo: number, ptr: number): RtObject | null {
    const s = this.script(scriptNo);
    if (!s) return null;
    for (const def of s.objects)
      if (def.offset + 12 === ptr) return this.instantiate(scriptNo, def);
    return null;
  }

  private varRef(kind: number, index: number, scriptNo: number, f: Frame):
      { get(): number; set(v: number): void } | null {
    if (kind === 0) {
      const g = this.globals;
      if (index < 0 || index >= g.length) return null;
      return { get: () => g[index], set: (v) => { g[index] = v; } };
    }
    if (kind === 1) {
      const l = this.localsOf(scriptNo);
      if (index < 0 || index >= l.length) return null;
      return { get: () => l[index], set: (v) => { l[index] = v; } };
    }
    // Temps and params live in a bounded window of the value stack.  A
    // garbage index must be refused, not written: `stack[i] = v` on a
    // JS array happily grows it to any index, and one bad write turns
    // the stack into a huge sparse array that makes every later
    // operation crawl.  That, not an infinite loop, was the hang.
    const base = kind === 2 ? f.tempsBase : f.paramsBase;
    if (index < 0 || index >= FRAME_WINDOW) return null;
    const i = base + index;
    if (i < 0 || i >= this.stack.length + FRAME_WINDOW) return null;
    return {
      get: () => this.stack[i] ?? 0,
      set: (v) => {
        while (this.stack.length <= i) this.stack.push(0);   // dense growth only
        this.stack[i] = v;
      },
    };
  }

  /**
   * Run until the starting frame returns, a limit trips, or the machine
   * cannot continue.
   *
   * One loop, one explicit frame stack, no JavaScript recursion: a game's
   * main loop iterates by sending to itself, so recursing per send would
   * grow the JS stack without bound and cap how long a game can run.
   */
  /**
   * Run until the starting frame returns, a limit trips, or the machine
   * cannot continue.
   *
   * `resume` continues an earlier run instead of starting one: a game's
   * main loop never returns, so playing it means executing a slice per
   * displayed frame and picking up exactly where the last slice stopped.
   * When a slice runs out of budget the frames are left standing for
   * that reason -- unwinding them would restart the game every frame.
   */
  run(scriptNo: number, obj: RtObject | null, pc: number,
      opts: { steps?: number; trace?: number; deadline?: number;
              paramsBase?: number; resume?: boolean; keep?: boolean;
              nested?: boolean } = {}): RunResult {
    const limit = opts.steps ?? 20000;
    const deadline = opts.deadline ?? (Date.now() + 250);
    const keepTrace = opts.nested ? this.trace : [];
    if (!opts.nested) { this.traceLimit = opts.trace ?? 0; this.trace = []; }
    const res: RunResult = {
      steps: 0, stopped: 'step-limit', kernelCalls: new Map(),
      unresolvedSends: 0, unresolvedKind: new Map(), maxStack: 0, maxDepth: 0,
      budget: limit, deadline,
    };
    // A fresh cycle is where a disposed clone is actually collected,
    // which is late enough for the cycle that disposed it to finish
    // using it.
    // A nested call is inside a cycle, not the start of one: sweeping
    // there would collect clones the cycle is still using.
    if (!opts.resume && !opts.nested) {
      for (const h of this.disposed) this.clones.delete(h);
      this.disposed.clear();
      // Scripts that asked to go while they were running have finished.
      for (const n of this.unloadPending) this.unloadScript(n);
      this.unloadPending.clear();
    }
    const base = opts.resume ? 0 : this.frames.length;
    const floor = opts.resume ? 0 : this.stack.length;
    if (!opts.resume) {
      // A frame nobody called still needs a well-formed argument block.
      // Without one, paramsBase points at whatever the method itself
      // pushes first, and `&rest` reads that as the argument count.
      let paramsBase = opts.paramsBase;
      if (paramsBase === undefined) { paramsBase = this.stack.length; this.stack.push(0); }
      this.frames.push({ scriptNo, obj, pc, tempsBase: this.stack.length,
                         paramsBase, argc: this.stack[paramsBase] ?? 0 });
    }
    if (!this.frames.length) { res.stopped = 'ret'; return res; }

    if (opts.nested) this.trace = keepTrace;
    let yielded = false;
    while (res.steps < limit) {
      if ((res.steps & 0x0F) === 0 && Date.now() > deadline) {
        res.stopped = 'timeout'; break;
      }
      // `RestartGame` has been called: give up this cycle wherever it
      // is, frames and all, and let the session build the game again.
      if (this.restartRequested) { res.stopped = 'restart'; break; }
      const f = this.frames[this.frames.length - 1];
      res.maxDepth = Math.max(res.maxDepth, this.frames.length - base);
      res.maxStack = Math.max(res.maxStack, this.stack.length);

      // Resume work interrupted by a method call.
      if (f.kcalls) {
        if (this.stepKernelCalls(f)) continue;    // pushed a frame
      }
      if (f.pending) {
        if (this.stepSend(f, res)) continue;      // pushed a frame
      }

      const s = this.script(f.scriptNo);
      if (!s) { res.stopped = 'error'; res.detail = `script ${f.scriptNo} missing`; break; }
      const ins = decode(s.data, f.pc);
      if (!ins) { res.stopped = 'invalid-opcode'; res.detail = `pc ${f.pc}`; break; }
      res.steps++;
      if (this.stack.length > MAX_STACK) {
        res.stopped = 'error';
        res.detail = 'stack overflow: ' + this.frameDump(base);
        break;
      }
      if (this.frames.length - base > MAX_FRAMES) {
        res.stopped = 'error'; res.detail = 'call depth exceeded'; break;
      }
      if (this.trace.length < this.traceLimit)
        this.trace.push(`${f.pc.toString(16).padStart(4, '0')} ${ins.name} ${ins.args.join(',')}`);
      watch(`s${f.scriptNo} pc=${f.pc} ${ins.name} depth=${this.frames.length} ` +
            `steps=${res.steps} stack=${this.stack.length}`);
      if (this.sampleEvery && res.steps % this.sampleEvery === 0) {
        const parts: string[] = [];
        for (let i = Math.max(base, this.frames.length - 3); i < this.frames.length; i++) {
          const g = this.frames[i];
          parts.push(`s${g.scriptNo}:${g.pc.toString(16)}${g.obj ? '/' + g.obj.name : ''}`);
        }
        const k = parts.join(' < ');
        this.samples.set(k, (this.samples.get(k) ?? 0) + 1);
      }

      const next = f.pc + ins.length;
      f.pc = next;
      const a = ins.args;
      const op = s.data[ins.pc] >> 1;
      const st = this.stack;

      try {
        if (op >= 0x40) {
          const rel = op - 0x40;
          const grp = rel >> 4, rest = rel & 0x0F;
          const kind = rest & 3, toStack = (rest >> 2) & 1, indexed = (rest >> 3) & 1;
          const idx = a[0] + (indexed ? this.acc : 0);
          const ref = this.varRef(kind, idx, f.scriptNo, f);
          /**
           * A variable outside its block is not fatal either.
           *
           * The same laxity as the property above, and the games lean
           * on it the same way -- KQ4's `copyProtect` reads local 0 of
           * a script that has no locals before the game has begun.
           * SCI's own fallback differs from the property one, though:
           * a denied read gives back the accumulator rather than zero,
           * and a denied write simply does not happen.  The value of a
           * store still has to come off the stack, or everything
           * pushed after it is read one slot out.
           */
          if (!ref) {
            this.oobVars++;
            if (grp === 0) { if (toStack) st.push(this.acc); }
            else if (grp === 1) { if (toStack || indexed) st.pop(); }
            else if (toStack) st.push(this.acc);
            break;
          }
          if (grp === 0) { const v = ref.get(); if (toStack) st.push(v); else this.acc = v; }
          else if (grp === 1) {
            // An indexed store takes its index from the accumulator, so
            // the value can only come from the stack -- the `a` in
            // `sati` names where the index is, not where the value is.
            // Reading the accumulator for both stored the index over
            // the value: `Print` builds its buttons with
            // `buttons[i] = (DButton new: ...)` and every one of them
            // came out as the loop counter, so the game's opening menu
            // had a title and no buttons to press.
            const v = (toStack || indexed) ? (st.pop() ?? 0) : this.acc;
            ref.set(v);
            // An indexed store is an expression: the compiler needs the
            // accumulator for the index, so it pushes the value, and
            // what it assigned has to come back out.  `Print` writes
            // `(buttons[i] = (DButton new:)) text: ... value: ...` --
            // the send that follows takes its receiver from here.
            if (indexed) this.acc = v;
          }
          else { const v = ref.get() + (grp === 2 ? 1 : -1); ref.set(v);
                 if (toStack) st.push(v); else this.acc = v; }
          continue;
        }

        switch (ins.name) {
          /**
           * The bitwise operations are 16-bit, like the machine.
           *
           * `shr` is a logical shift, not an arithmetic one: `0x8000
           * >> 3` is `0x1000` on SCI's word, and carrying the sign bit
           * along instead makes it `0xfffff000`.  That is not a
           * rounding error, it is every higher bit set.  Camelot keeps
           * its story flags sixteen to a global and sets one with
           * `flags |= (0x8000 >> n)`, so setting flag 13 set flags 0
           * to 13 at a stroke -- among them "Arthur is wearing his
           * armour", which is why he began the game in chain mail
           * instead of the tunic he wakes up in.
           */
          case 'bnot': this.acc = s16(~this.acc & 0xFFFF); break;
          case 'add': this.acc = (st.pop() ?? 0) + this.acc; break;
          case 'sub': this.acc = (st.pop() ?? 0) - this.acc; break;
          case 'mul': this.acc = (st.pop() ?? 0) * this.acc; break;
          case 'div': { const d = this.acc; this.acc = d ? Math.trunc((st.pop() ?? 0) / d) : 0; break; }
          case 'mod': { const d = this.acc; this.acc = d ? (st.pop() ?? 0) % d : 0; break; }
          case 'shr': {
            const v = (st.pop() ?? 0) & 0xFFFF, k = this.acc & 0xFFFF;
            this.acc = s16(k >= 16 ? 0 : (v >>> k) & 0xFFFF);
            break;
          }
          case 'shl': {
            const v = (st.pop() ?? 0) & 0xFFFF, k = this.acc & 0xFFFF;
            this.acc = s16(k >= 16 ? 0 : (v << k) & 0xFFFF);
            break;
          }
          case 'xor': this.acc = (st.pop() ?? 0) ^ this.acc; break;
          case 'and': this.acc = (st.pop() ?? 0) & this.acc; break;
          case 'or':  this.acc = (st.pop() ?? 0) | this.acc; break;
          case 'neg': this.acc = -this.acc; break;
          case 'not': this.acc = this.acc ? 0 : 1; break;
          case 'eq?': this.prev = this.acc; this.acc = (st.pop() ?? 0) === this.acc ? 1 : 0; break;
          case 'ne?': this.prev = this.acc; this.acc = (st.pop() ?? 0) !== this.acc ? 1 : 0; break;
          case 'gt?': this.prev = this.acc; this.acc = (st.pop() ?? 0) > this.acc ? 1 : 0; break;
          case 'ge?': this.prev = this.acc; this.acc = (st.pop() ?? 0) >= this.acc ? 1 : 0; break;
          case 'lt?': this.prev = this.acc; this.acc = (st.pop() ?? 0) < this.acc ? 1 : 0; break;
          case 'le?': this.prev = this.acc; this.acc = (st.pop() ?? 0) <= this.acc ? 1 : 0; break;
          /**
           * Unsigned comparison, where a pointer is a large address.
           *
           * This is how the scripts tell a pointer from a small number,
           * and they do it on purpose: script 255's `Print` treats
           * anything under 1000 as a text module and everything else as
           * a string to copy.  Truncating a reference to sixteen bits
           * throws the tag away and leaves the offset, so KQ4's pointer
           * to "Enter input" at offset 618 read as module 618 and the
           * parser came up as an empty box with nothing to type into.
           * `ucmp` has the rule.
           */
          case 'ugt?': this.prev = this.acc; this.acc = ucmp(st.pop() ?? 0, this.acc) > 0 ? 1 : 0; break;
          case 'uge?': this.prev = this.acc; this.acc = ucmp(st.pop() ?? 0, this.acc) >= 0 ? 1 : 0; break;
          case 'ult?': this.prev = this.acc; this.acc = ucmp(st.pop() ?? 0, this.acc) < 0 ? 1 : 0; break;
          case 'ule?': this.prev = this.acc; this.acc = ucmp(st.pop() ?? 0, this.acc) <= 0 ? 1 : 0; break;
          case 'bt': if (this.acc) f.pc = next + a[0]; break;
          case 'bnt': if (!this.acc) f.pc = next + a[0]; break;
          case 'jmp': f.pc = next + a[0]; break;
          case 'ldi': this.acc = a[0]; break;
          case 'push': st.push(this.acc); break;
          case 'selfID': this.acc = f.obj?.handle ?? 0; break;
          case 'pushSelf': st.push(f.obj?.handle ?? 0); break;
          case 'pushi': st.push(a[0]); break;
          case 'push0': st.push(0); break;
          case 'push1': st.push(1); break;
          case 'push2': st.push(2); break;
          case 'toss': st.pop(); break;
          case 'dup': st.push(st[st.length - 1] ?? 0); break;
          case 'pprev': st.push(this.prev); break;
          case 'link':
            // The temps start empty, and so does the text behind them.
            this.clearStackText(st.length, a[0]);
            for (let i = 0; i < a[0]; i++) st.push(0);
            break;
          case 'class': {
            // Names the class object for a species, which is how a script
            // sends to a class it does not hold a reference to.
            const l = this.species.locate(a[0]);
            this.acc = l && this.objectAt(l.script, l.offset + 12)
              ? makeRef(l.script, l.offset + 12) : 0;
            break;
          }
          case 'lea': {
            // The address of a variable, which is how a script hands the
            // kernel somewhere to write: `Format` and `GetFarText` are
            // both given a buffer this way.  There is no byte-addressable
            // script memory for a variable here, so each slot gets a
            // stable handle standing in for its address -- returning zero
            // instead, as this did, makes every formatted string null.
            const kind = (a[0] >> 1) & 3;
            const idx = a[1] + ((a[0] & 0x10) ? this.acc : 0);
            this.acc = this.bufferFor(kind, idx, f.scriptNo, f);
            break;
          }

          case 'lofsa': case 'lofss': {
            /**
             * The address of something in this script -- an object, or
             * a string literal.
             *
             * Always tagged with the script it came from, objects and
             * strings alike.  A bare offset says nothing about where it
             * points, and these pointers travel: Camelot's script 100
             * hands "Camelot Game Options:" to the dialog code in
             * script 255, which reads it back in a frame of its own.
             * Resolving against whatever script happens to be running
             * then lands in the wrong resource, and the game's opening
             * menu came up an empty box eight pixels wide.
             */
            const off = next + a[0];
            const v = makeRef(f.scriptNo, off);
            if (ins.name === 'lofsa') this.acc = v; else st.push(v);
            break;
          }

          case 'pToa': case 'pTos': case 'aTop': case 'sTop':
          case 'ipToa': case 'dpToa': case 'ipTos': case 'dpTos': {
            if (!f.obj) { res.stopped = 'error'; res.detail = 'property access with no self'; break; }
            const pi = a[0] >> 1;
            const n = ins.name;
            /**
             * A property the object does not have reads as zero.
             *
             * Refusing it kills games that are not broken.  SCI did no
             * checking at all -- the offset was added to the object's
             * address and whatever lay there was used -- and Sierra's
             * own compiler let an invalid property symbol through in
             * `Act::canBeHere`, which is in script 998 of several
             * games.  Hero's Quest has it, and so does Iceman: the
             * method runs during the speed test before the title is
             * even up, so the whole game stopped on the first frame
             * with `property 26044 out of range`.
             *
             * Zero is what the games get away with, since the value is
             * only ever tested against a flag.  A write goes nowhere
             * rather than growing the object.
             */
            const bad = pi < 0 || pi >= f.obj.props.length;
            if (bad) {
              this.oobProps++;
              if (n === 'pToa' || n === 'ipToa' || n === 'dpToa') this.acc = 0;
              else if (n === 'pTos' || n === 'ipTos' || n === 'dpTos') st.push(0);
              else if (n === 'sTop') st.pop();
              break;
            }
            if (n === 'pToa') this.acc = f.obj.props[pi];
            else if (n === 'pTos') st.push(f.obj.props[pi]);
            else if (n === 'aTop') f.obj.props[pi] = PMachine.word(this.acc);
            else if (n === 'sTop') f.obj.props[pi] = PMachine.word(st.pop() ?? 0);
            else {
              const d = (n === 'ipToa' || n === 'ipTos') ? 1 : -1;
              f.obj.props[pi] += d;
              if (n === 'ipToa' || n === 'dpToa') this.acc = f.obj.props[pi];
              else st.push(f.obj.props[pi]);
            }
            break;
          }

          case 'callk': {
            // The operand counts argument *bytes*, but the caller also
            // pushes the argument count itself ahead of them -- the same
            // convention `call`/`callb`/`calle` handle with their `- 1`.
            // Popping only the arguments leaks one slot per kernel call,
            // which a game's main loop turns into a steady stack climb.
            /**
             * `&rest` belongs to the send, not to a kernel call on the way.
             *
             * Early SCI0 does not count `&rest` towards a kernel call's
             * arguments, and its compiler relies on that: `Collect::
             * firstTrue` pushes the selector, the count and `&rest`, then
             * calls `NodeValue` to get the element, and only then sends.
             * Letting the kernel call swallow the pending rest took the
             * send's own arguments off the stack with it, so the send that
             * followed dispatched nothing at all -- KQ4's dialogs never
             * found the item to type into, and the copy-protection prompt
             * could not be answered.  Later games emit no kernel call
             * between the two and are unaffected either way.
             */
            const rest = this.index.selectorShift ? 0 : this.restAdjust;
            const words = (a[1] >> 1) + rest;
            const pBase = st.length - words - 1;
            if (pBase < 0) { res.stopped = 'error'; res.detail = 'callk: params underflow'; break; }
            st[pBase] = words;
            // `Wait` is the game saying it has finished a cycle and wants
            // the rest of its frame back.  It blocks on real hardware, so
            // it has to block here: the instruction is left un-executed
            // and the slice ends, and the same `Wait` runs again next
            // frame until enough ticks have gone by.  Returning
            // immediately instead lets a game run its whole cycle as many
            // times as the instruction budget allows, which is why
            // everything moved far too fast.
            if (this.index.kernelName(a[0]) === 'MenuSelect') {
              // Blocks on real hardware; here it takes a frame at a
              // time and the instruction is run again until it answers.
              const r = this.menuStep(st[pBase + 1] ?? 0);
              if (r === null) { f.pc = ins.pc; yielded = true; break; }
              if (rest) this.restAdjust = 0;   // untouched when the send still needs it
              st.splice(pBase, words + 1);
              this.acc = r;
              break;
            }
            if (this.index.kernelName(a[0]) === 'Wait') {
              const asked = st[pBase + 1] ?? 0;
              const want = asked > 0 ? asked : this.minWait;
              if (this.ticks - this.lastWait < want) {
                f.pc = ins.pc;          // run this same Wait again next slice
                yielded = true;
                break;
              }
            }
            if (rest) this.restAdjust = 0;   // untouched when the send still needs it
            const args = st.splice(pBase, words + 1).slice(1);
            res.kernelCalls.set(a[0], (res.kernelCalls.get(a[0]) ?? 0) + 1);
            this.acc = this.kernel(a[0], args, f);
            break;
          }

          case 'send': case 'self': case 'super': {
            const rest = this.restAdjust;
            const words = Math.max(0, a[a.length - 1] >> 1) + rest;
            this.restAdjust = 0;
            const args = st.splice(st.length - words, words);
            if (rest) this.widenLastGroup(args, rest);
            const target = ins.name === 'send' ? this.resolveTarget(f, this.acc) : f.obj;
            if (!target) {
              const v = this.acc;
              const kind = ins.name !== 'send' ? 'no self'
                : v === 0 ? 'target 0 (uninitialised)'
                : isRef(v) ? 'tagged ref, no object'
                : (v > 0 && v < 65536) ? 'bare offset, no object' : 'other';
              res.unresolvedKind.set(kind, (res.unresolvedKind.get(kind) ?? 0) + 1);
              res.unresolvedSends++;
              break;
            }
            f.pending = { target, args, i: 0,
                          fromSpecies: ins.name === 'super' ? a[0] : undefined };
            this.stepSend(f, res);
            break;
          }

          case 'call': case 'callb': case 'calle': {
            const words = Math.max(0, a[a.length - 1] >> 1) + this.restAdjust;
            this.restAdjust = 0;
            const pBase = st.length - words - 1;
            if (pBase < 0) { res.stopped = 'error'; res.detail = `${ins.name}: params underflow`; break; }
            // A call's count word is simply however many words were
            // pushed, so `&rest` needs no separate bookkeeping here.
            st[pBase] = words;
            let targetScript = f.scriptNo, targetPc = -1;
            if (ins.name === 'call') targetPc = next + a[0];
            else {
              targetScript = ins.name === 'callb' ? 0 : a[0];
              targetPc = this.exportOffset(targetScript, ins.name === 'callb' ? a[0] : a[1]);
            }
            if (targetPc < 0) { st.length = pBase; this.acc = 0; res.unresolvedSends++; break; }
            this.frames.push({ scriptNo: targetScript, obj: f.obj, pc: targetPc,
                               tempsBase: st.length, paramsBase: pBase,
                               argc: st[pBase] ?? 0 });
            break;
          }

          case '&rest': {
            // argc is a stack value, so it must be sanity-checked before
            // being used as a loop bound.
            const argc = this.stack[f.paramsBase] ?? 0;
            if (argc < 0 || argc > FRAME_WINDOW) break;
            let pushed = 0;
            for (let i = a[0]; i <= argc; i++) { st.push(this.stack[f.paramsBase + i] ?? 0); pushed++; }
            // The count word for the call being built has to grow by the
            // same amount, but it is not at a fixed distance from here:
            // it sits below whatever arguments were pushed explicitly
            // first.  `(mover init: self &rest 2)` pushes one, and
            // reaching past it lands on that argument and corrupts it
            // instead -- which is how the ego came to be given a mover
            // whose client was a number that resolved to nothing.  Only
            // the instruction that consumes these knows the layout, so
            // the count is recorded and fixed up there.
            this.restAdjust += pushed;
            break;
          }

          case 'ret': {
            const done = this.frames.pop()!;
            st.length = Math.max(floor, Math.min(st.length, done.paramsBase));
            if (this.frames.length <= base) res.stopped = 'ret';
            break;
          }

          default:
            res.stopped = 'unimplemented'; res.detail = ins.name;
        }
      } catch (e) {
        res.stopped = 'error'; res.detail = (e as Error).message;
      }
      if (yielded || res.stopped !== 'step-limit') break;
    }

    // A run that merely ran out of budget still has a story to tell:
    // where it was when the budget ended.
    if (res.stopped === 'step-limit' || res.stopped === 'timeout')
      res.detail = this.frameDump(base);
    else if (res.stopped === 'error' || res.stopped === 'invalid-opcode')
      res.detail = `${res.detail ?? ''} at ${this.frameDump(base)}`;
    const ranOut = res.stopped === 'step-limit' || res.stopped === 'timeout';
    if (!(opts.keep && ranOut)) {
      while (this.frames.length > base) this.frames.pop();
      this.stack.length = floor;
    }
    return res;
  }

  /**
   * Where the value stack went.  A frame that never gives its slots back
   * shows up as a large gap between its own base and the next frame's,
   * which names the method to look at.
   */
  frameDump(base: number): string {
    const parts: string[] = [];
    for (let i = base; i < this.frames.length; i++) {
      const f = this.frames[i];
      const top = i + 1 < this.frames.length
        ? this.frames[i + 1].paramsBase : this.stack.length;
      parts.push(`[s${f.scriptNo} ${f.obj?.name ?? '-'} pc=${f.pc.toString(16)}` +
                 ` p=${f.paramsBase} t=${f.tempsBase} grew=${top - f.tempsBase}]`);
    }
    return parts.join(' ');
  }

  /**
   * Advance one send's selector groups.  Property gets and sets are done
   * here and now; a method pushes a frame and returns true so the main
   * loop runs it, resuming this cursor when it returns.
   */
  private stepSend(f: Frame, res: RunResult): boolean {
    const p = f.pending!;
    while (p.i + 1 < p.args.length) {
      const sel = p.args[p.i], argc = p.args[p.i + 1];
      if (!Number.isInteger(argc) || argc < 0 || argc > 127) break;
      const params = p.args.slice(p.i + 2, p.i + 2 + argc);
      p.i += 2 + argc;

      /**
       * Early SCI0 flags a property access in the low bit.
       *
       * Those games store selector ids as byte offsets -- twice the
       * table index, so always even -- and a send that means "read or
       * write this property" rather than "call this method" arrives
       * with bit 0 set.  `Index.selectorShift` already knows which
       * games those are, because the same builds carry the extra
       * leading word in their scripts.
       *
       * Left unmasked, every property send in KQ4 matched nothing and
       * returned zero.  `Dialog::setSize` walks its items asking each
       * for `nsLeft` and `nsTop`, took nought for all of them, and
       * opened a window four pixels square with the question drawn
       * outside it -- a black screen with a white band across the top.
       * The same zero reached the modal loop, which read its event's
       * type as nothing whatever arrived and so span for ever: the
       * copy-protection prompt could not be seen, answered or escaped.
       */
      const psel = (this.index.selectorShift && (sel & 1)) ? sel & ~1 : sel;
      const pi = p.fromSpecies === undefined ? p.target.indexOfSelector(psel) : -1;
      if (pi >= 0) {
        if (argc === 0) this.acc = p.target.props[pi];
        else p.target.props[pi] = PMachine.word(params[0]);
        continue;
      }
      const found = p.fromSpecies !== undefined
        ? this.species.lookupFrom(p.fromSpecies, sel)
        : this.species.lookup(p.target.def, sel, p.target.scriptNo);
      if (!found) {
        // A selector the object does not answer returns nothing, and
        // "nothing" has to be zero: leaving the accumulator alone lets
        // whatever was in it stand as the result, and a caller like
        // `firstTrue` reads that as success.
        res.unresolvedSends++;
        this.acc = 0;
        continue;
      }
      const pBase = this.stack.length;
      this.stack.push(argc, ...params);
      this.frames.push({ scriptNo: found.script, obj: p.target, pc: found.offset,
                         tempsBase: this.stack.length, paramsBase: pBase, argc });
      return true;
    }
    f.pending = undefined;
    return false;
  }

  /**
   * How far a mover's client should move this cycle.
   *
   * A straight line to the target, limited to the client's own step in
   * whichever axis dominates, and landing exactly on the target once it
   * is within one step.  Working it out from the current position each
   * cycle rather than accumulating a stored increment keeps the path
   * straight without rounding drift, and means a client nudged by
   * anything else simply carries on from where it now is.
   */
  /**
   * Set up the line a mover will walk its client along.
   *
   * The dominant axis takes a whole step each cycle and the other is
   * nudged when the error term says so, which is what makes the last
   * step land on the target rather than near it.  `i1` and `i2` are the
   * two amounts the error moves by and `di` is the error itself; they
   * are doubled so the arithmetic stays whole.
   *
   * The step is reduced until the shorter axis can keep up.  Without
   * that a diagonal with a long dominant axis moves the other one by
   * more than its own step allows, and the actor arrives sideways.
   */
  private initBresen(mover: RtObject, client: RtObject, mult: number) {
    const cx = s16(u16(this.prop(client, 'x')));
    const cy = s16(u16(this.prop(client, 'y')));
    const deltaX = s16(u16(this.prop(mover, 'x', cx))) - cx;
    const deltaY = s16(u16(this.prop(mover, 'y', cy))) - cy;
    let xStep = Math.max(1, Math.abs(s16(u16(this.prop(client, 'xStep', 3))))) * mult;
    const yStep = Math.max(1, Math.abs(s16(u16(this.prop(client, 'yStep', 2))))) * mult;
    let dx = 0, dy = 0, i1 = 0, i2 = 0, di = 0, incr = 1, onX = 0;
    for (;;) {
      if (Math.abs(deltaX) >= Math.abs(deltaY)) {
        onX = 1;
        dx = deltaX < 0 ? -xStep : xStep;
        dy = deltaX !== 0 ? Math.trunc(dx * deltaY / deltaX) : 0;
        incr = 1;
        i1 = 2 * (dx * deltaY - dy * deltaX);
        if (deltaY < 0) { incr = -1; i1 = -i1; }
        i2 = i1 - 2 * deltaX;
        di = i1 - deltaX;
        if (deltaX < 0) { i1 = -i1; i2 = -i2; di = -di; }
      } else {
        onX = 0;
        dy = deltaY < 0 ? -yStep : yStep;
        dx = deltaY !== 0 ? Math.trunc(dy * deltaX / deltaY) : 0;
        incr = 1;
        i1 = 2 * (dy * deltaX - dx * deltaY);
        if (deltaX < 0) { incr = -1; i1 = -i1; }
        i2 = i1 - 2 * deltaY;
        di = i1 - deltaY;
        if (deltaY < 0) { i1 = -i1; i2 = -i2; di = -di; }
      }
      xStep--;
      if (!(xStep > yStep && xStep !== 0 && yStep < Math.abs(dy + incr))) break;
    }
    this.setProp(mover, 'dx', dx);
    this.setProp(mover, 'dy', dy);
    this.setProp(mover, 'b-i1', i1);
    this.setProp(mover, 'b-i2', i2);
    this.setProp(mover, 'b-di', di);
    this.setProp(mover, 'b-incr', incr);
    this.setProp(mover, 'b-xAxis', onX);
    this.setProp(mover, 'b-moveCnt', 0);
    this.setProp(mover, 'xLast', cx);
    this.setProp(mover, 'yLast', cy);
    this.setProp(mover, 'completed', 0);
  }


  /**
   * An edit field: what has been typed, and the caret.
   *
   * The caret goes where the cursor actually is rather than always at
   * the end, so moving through the line with the arrow keys shows.
   */
  /**
   * An edit field: a box, what has been typed, and the caret.
   *
   * SCI draws it as a rectangle one pixel outside the control's own,
   * erased and then framed, with the text inset by two -- so the field
   * you type into is visibly a field, rather than words loose on the
   * window.  The caret goes where the cursor actually is rather than
   * always at the end, so moving along the line with the arrow keys
   * shows.
   */
  /**
   * The saved-game list, which is a control like any other.
   *
   * `text` points at the first of a run of fixed-width entries -- the
   * width is the control's own `x`, thirty-six for every SCI0 save
   * dialog -- ended by an empty one.  `cursor` and `lsTop` are pointers
   * into that same run, not indices, so which line is picked and which
   * is at the top are both found by subtracting.
   *
   * The furniture is ScummVM's reading of the original: a frame around
   * the whole, an up arrow at the top and a down arrow at the bottom
   * (characters 24 and 25 of the font), and a second frame around the
   * lines between them.  The picked line is drawn in reverse.
   */
  private drawList(o: RtObject, x: number, y: number, w: number, bottom: number,
                   font: Font | null, pen = 0, back = 15) {
    if (!font) return;
    const base = this.prop(o, 'text');
    const stride = this.prop(o, 'x', SAVE_NAME_LEN) || SAVE_NAME_LEN;
    const entries: string[] = [];
    for (let i = 0; i < MAX_SAVES; i++) {
      const t = this.stringAt(base + i * stride, o.scriptNo);
      if (!t) break;
      entries.push(t);
    }
    const index = (ptr: number) =>
      !ptr || ptr < base ? 0 : Math.floor((ptr - base) / stride);
    const top = index(this.prop(o, 'lsTop'));
    const cursor = index(this.prop(o, 'cursor'));
    const h = Math.max(8, font.lineHeight);
    this.screen.fill(x, y, x + w, bottom, back);
    this.screen.frame(x - 1, y - 1, x + w + 1, bottom + 1, pen);
    // The arrows sit in the nine pixels at each end, and the lines run
    // between them.
    // In the font the port is using, not the one the list is set to:
    // ScummVM draws the arrows before it switches fonts, and the dialogs
    // set the list to font 4, whose characters 24 and 25 are blank.
    const sys = this.font(0) ?? font;
    const arrow = (c: string, ty: number) => {
      const wide = sys.chars[c.charCodeAt(0)]?.width ?? 0;
      this.screen.text(sys, c, x + Math.max(0, (w - wide) >> 1), ty, pen);
    };
    arrow('\x18', y);
    arrow('\x19', bottom - 9);
    this.screen.frame(x, y + 9, x + w, bottom - 9, pen);
    for (let i = top, ty = y + 10; i < entries.length && ty + h <= bottom - 10; i++, ty += h) {
      const line = entries[i].slice(0, stride);
      if (i === cursor) {
        this.screen.fill(x + 1, ty, x + w - 1, ty + h, pen);
        this.screen.text(font, line, x + 2, ty, back);
      } else {
        this.screen.text(font, line, x + 2, ty, pen);
      }
    }
  }

  private drawEditField(o: RtObject, x: number, y: number, w: number,
                        font: Font | null, pen = 0, back = 15) {
    if (!font) return;
    const text = this.stringAt(this.prop(o, 'text'), o.scriptNo);
    const h = Math.max(8, font.lineHeight);
    if (w <= 0) return;
    // Erase and frame the box.  It is redrawn on every keystroke, and
    // text left behind would show through wherever the new line is
    // shorter than the old.
    this.screen.fill(x - 1, y - 1, x + w + 1, y + h + 1, back);
    this.screen.frame(x - 1, y - 1, x + w + 1, y + h + 1, pen);
    const tx = x + 1;
    this.screen.text(font, text, tx, y, pen);
    const cur = Math.max(0, Math.min(text.length, this.prop(o, 'cursor', text.length)));
    let cx = tx;
    for (let i = 0; i < cur; i++) cx += font.chars[text.charCodeAt(i)]?.width ?? 0;
    this.screen.fill(cx, y, cx + 1, y + h, pen);
  }

  /**
   * Draw a control where it sits, after something has changed it.
   *
   * A control's rectangle is relative to the window it belongs to, so
   * the same offset the drawing path applies has to be applied here.
   */
  /**
   * Would the field still hold its text with one more character in it?
   *
   * `max` is not the whole of the limit.  SCI refuses a character on
   * width as well as on count: it measures the text with the new
   * character added and drops it if that reaches the control's
   * rectangle.  Both tests are needed because the box is not sized for
   * the worst case -- `DEdit::setSize` asks `TextSize` how wide "M" is
   * and then takes three quarters of `max` of them, on the assumption
   * that ordinary words average narrower than the widest letter.  For
   * Camelot's parser that is 8 pixels by 45 characters by 3/4, a field
   * 270 pixels wide holding a string that could be 360 pixels long, so
   * the count alone never stops anything and what is typed runs out of
   * the box and across the picture.
   *
   * Measured from the whole string rather than from the part before the
   * caret, which is what decides whether it all fits.
   */
  private fitsInField(o: RtObject, text: string, key: number): boolean {
    const fnt = this.font(this.prop(o, 'font')) ?? this.font(0);
    if (!fnt) return true;
    const width = s16(u16(this.prop(o, 'nsRight'))) - s16(u16(this.prop(o, 'nsLeft')));
    if (width <= 0) return true;
    let w = fnt.chars[key]?.width ?? 0;
    for (const c of text) w += fnt.chars[c.charCodeAt(0)]?.width ?? 0;
    return w < width;
  }

  private redrawControl(o: RtObject) {
    const p = this.port;
    const x = p.x + this.prop(o, 'nsLeft');
    const y = p.y + this.prop(o, 'nsTop');
    const w = Math.max(0, this.prop(o, 'nsRight') - this.prop(o, 'nsLeft'));
    this.drawEditField(o, x, y, w, this.font(this.prop(o, 'font')) ?? this.font(0),
                       p.pen ?? 0, p.back ?? 15);
  }

  /**
   * Move an event between screen and window coordinates.
   *
   * A control's rectangle is relative to the window it sits in, so a
   * dialog converts the event before asking which control was hit.
   * Passing the coordinates through unchanged -- which is what this did,
   * on the grounds that one port covered the whole picture -- tests the
   * click against the wrong rectangles, and Camelot's opening menu could
   * only be worked with the keyboard.
   */
  private shiftEvent(ref: number, sign: number): number {
    const ev = this.resolveTarget(null, ref);
    if (!ev) return 0;
    const p = this.port;
    this.setProp(ev, 'x', s16(u16(this.prop(ev, 'x'))) + sign * p.x);
    this.setProp(ev, 'y', s16(u16(this.prop(ev, 'y'))) + sign * p.y);
    return ref;
  }

  /**
   * One frame of the menu, for `MenuSelect`.
   *
   * The kernel blocks on real hardware: it opens the menus and runs its
   * own loop until the player picks something.  Nothing here can block,
   * so this does one frame's worth and says whether it is finished --
   * `null` means "still open", and the interpreter runs the same
   * `MenuSelect` again next frame, the way it already does for `Wait`.
   *
   * Returns the chosen item as (menu << 8) | item, both counting from
   * one, or -1 when the player backed out.
   */
  menuStep(evRef: number): number | null {
    const ev = this.resolveTarget(null, evRef);
    const font = this.font(0);
    if (this.menu.openMenu < 0) {
      if (!ev) return -1;
      const type = u16(this.prop(ev, 'type'));
      const message = u16(this.prop(ev, 'message'));
      const y = s16(u16(this.prop(ev, 'y')));
      // A shortcut picks its item without the menus ever appearing.
      const direct = type === EV.keyboard ? this.menu.forKey(message) : 0;
      if (direct) { this.setProp(ev, 'claimed', 1); return direct; }
      if (!this.menu.menus.length) return -1;
      if (!this.menu.activates(type, message, y)) return -1;
      this.setProp(ev, 'claimed', 1);
      const at = type === EV.mouseDown ? this.menu.menuAt(s16(u16(this.prop(ev, 'x')))) : 0;
      this.menu.open(this.screen, font, at < 0 ? 0 : at);
      return null;
    }
    // Open: spend this frame's events on it.
    while (this.events.length) {
      const e = this.events.shift()!;
      if (e.type === EV.keyboard) {
        if (e.message === 27) { this.menu.close(this.screen, font); return -1; }
        if (e.message === 13) {
          const id = this.menu.chosen();
          if (id) { this.menu.close(this.screen, font); return id; }
          continue;
        }
        if (e.message === 0x4B00) this.menu.move(this.screen, font, -1, 0);
        else if (e.message === 0x4D00) this.menu.move(this.screen, font, 1, 0);
        else if (e.message === 0x4800) this.menu.move(this.screen, font, 0, -1);
        else if (e.message === 0x5000) this.menu.move(this.screen, font, 0, 1);
      } else if (e.type === EV.mouseDown || e.type === EV.mouseUp) {
        const overBar = e.y < 0 ? this.menu.menuAt(e.x) : -1;
        if (overBar >= 0 && overBar !== this.menu.openMenu) {
          this.menu.move(this.screen, font, overBar - this.menu.openMenu, 0);
        } else {
          const it = this.menu.itemAt(font, e.x, e.y);
          if (it >= 0 && it !== this.menu.openItem)
            this.menu.move(this.screen, font, 0, it - this.menu.openItem);
          if (e.type === EV.mouseUp) {
            const id = it >= 0 ? this.menu.chosen() : 0;
            this.menu.close(this.screen, font);
            return id || -1;
          }
        }
      }
    }
    return null;
  }

  /**
   * The compiled pattern a `Said` argument points at.
   *
   * Patterns live in the script's said block, one after another and
   * terminated by 0xFF, and the reference carries the script it came
   * from -- which is why every pointer is tagged.
   */
  private saidSpec(ref: number): Uint8Array | null {
    if (!isRef(ref)) return null;
    const sc = this.index.script(refScript(ref));
    if (!sc) return null;
    const at = refOffset(ref);
    for (const [off, bytes] of sc.said) if (off === at) return bytes;
    // Not the start of a pattern, so read from here to the terminator.
    const end = sc.data.indexOf(0xFF, at);
    return end > at ? sc.data.subarray(at, end) : null;
  }

  /**
   * The strip of floor a cast member stands on.
   *
   * Worked out from where the member is now rather than read back from
   * its `br` properties, which only the members that run a full `doit`
   * keep up to date: SQ3's `motivator` sits at 183,169 carrying a base
   * rectangle left over from the origin, and trusting that would put an
   * invisible obstacle in the corner of the room and none where the
   * thing actually is.
   */
  private baseRectOf(o: RtObject, atX?: number, atY?: number) {
    const cel = this.celOf(o);
    if (!cel) return null;
    const x = atX ?? s16(u16(this.prop(o, 'x')));
    const y = atY ?? s16(u16(this.prop(o, 'y')));
    const r = this.celRect(cel, x, y, s16(u16(this.prop(o, 'z'))));
    const step = Math.max(1, s16(u16(this.prop(o, 'yStep', 2))));
    if (r.right <= r.left) return null;
    return { left: r.left, right: r.right, top: y + 1 - step, bottom: y + 1 };
  }

  /**
   * Would this actor's feet land on another cast member's?
   *
   * Actors stand on each other's base rectangles, not their pictures --
   * two characters may overlap on screen while standing apart.  A
   * member with the "ignore actors" bit is walked through on purpose,
   * which is how doorways work: Camelot's `door` carries it, its
   * `armourStand` and `pouch` do not.
   */
  private blockedByCast(o: RtObject, left: number, top: number,
                        right: number, bottom: number, listH: number): boolean {
    if (!listH) return false;
    // An actor that ignores others is not stopped by them either.
    if (u16(this.prop(o, 'signal')) & 0x4000) return false;
    for (const v of this.listValues(listH)) {
      const m = this.resolveTarget(null, v);
      if (!m || m === o) continue;
      const sig = u16(this.prop(m, 'signal'));
      if (sig & SIGNAL_NO_BLOCK) continue;
      const b = this.baseRectOf(m);
      if (!b) continue;                               // no base to stand on
      if (left < b.right && b.left < right && top < b.bottom && b.top < bottom) return true;
    }
    return false;
  }

  /**
   * May this actor stand on this rectangle?
   *
   * The only place the question is answered, because it is asked from
   * two directions and they must not drift apart.  They did.  The
   * kernel's `CanBeHere` had its "must fit inside the picture" test
   * taken out -- the edge of a picture is not a wall, and a room that
   * wants a way out simply leaves its edge unpainted -- but the test
   * inside `DoBresen`, which is the one every walk actually passes
   * through, kept its own copy.
   *
   * So the answer depended on who asked.  Merlin's room is left by
   * walking off the bottom, `Rm2::doit` watching for the ego's y to
   * pass 188; the ego steps two rows at a time and its base reaches one
   * row below its feet, so a step to y 190 puts the base at 191 and the
   * step was refused.  `CanBeHere` said that position was fine, and
   * putting the ego there by hand did leave the room -- it simply could
   * never walk there.  It stopped at 188 exactly, one short, in a room
   * with no other way out.  Gwenhyver's bower is the same shape: out
   * through the right-hand edge, `x` past 308.
   */
  private standable(o: RtObject, left: number, top: number, right: number,
                    bottom: number, cast: number): boolean {
    if (right <= left || bottom <= top) return true;   // no base yet
    if (this.blockedByCast(o, left, top, right, bottom, cast)) return false;
    const illegal = u16(this.prop(o, 'illegalBits'));
    if (!illegal) return true;
    return (this.controlBits(left, top, right, bottom) & illegal) === 0;
  }

  /**
   * Could this actor stand with its feet at (x, y)?
   *
   * The base rectangle is worked out for the position being considered
   * rather than read from the actor, so a step can be tested before it
   * is taken.
   */
  private legalAt(o: RtObject, x: number, y: number): boolean {
    const b = this.baseRectOf(o, x, y);
    if (!b) return true;
    return this.standable(o, b.left, b.top, b.right, b.bottom, this.cast);
  }

  /**
   * The set of control colours under a rectangle, one bit per colour.
   *
   * The whole base is sampled rather than a single point, because a foot
   * overlapping a wall by one pixel is what has to stop a walk.
   */
  private controlBits(left: number, top: number, right: number, bottom: number): number {
    const x0 = Math.max(0, Math.min(WIDTH, left));
    const x1 = Math.max(0, Math.min(WIDTH, right));
    const y0 = Math.max(0, Math.min(HEIGHT, top));
    const y1 = Math.max(0, Math.min(HEIGHT, bottom));
    let bits = 0;
    const map = this.screen.control;
    for (let y = y0; y < y1; y++) {
      const row = y * WIDTH;
      for (let x = x0; x < x1; x++) bits |= 1 << (map[row + x] & 15);
    }
    return bits;
  }

  /**
   * Grow the count of the last selector group by what `&rest` added.
   *
   * A send carries several (selector, count, args...) groups and `&rest`
   * widens only the one being built, which is the last.  Walking the
   * groups from the front is the only way to find its count word: from
   * the back, the arguments and the counts are indistinguishable.
   */
  private widenLastGroup(args: number[], rest: number) {
    const base = args.length - rest;
    let i = 0;
    while (i + 1 < args.length) {
      const n = args[i + 1];
      if (!Number.isInteger(n) || n < 0 || n > 127) return;
      if (i + 2 + n >= base) { args[i + 1] = n + rest; return; }
      i += 2 + n;
    }
  }

  /**
   * Dispatch the next call a kernel function scheduled, if any remain.
   * Members that do not answer the selector are simply skipped.
   */
  private stepKernelCalls(f: Frame): boolean {
    const k = f.kcalls!;
    while (k.i < k.items.length) {
      const it = k.items[k.i++];
      const found = this.species.lookup(it.target.def, it.sel, it.target.scriptNo);
      if (!found) continue;
      const pBase = this.stack.length;
      this.stack.push(it.params.length, ...it.params);
      this.frames.push({ scriptNo: found.script, obj: it.target, pc: found.offset,
                         tempsBase: this.stack.length, paramsBase: pBase,
                         argc: it.params.length });
      return true;
    }
    this.acc = k.result;
    f.kcalls = undefined;
    return false;
  }

  /**
   * Run one of an object's own methods and hand back what it returned.
   *
   * A kernel that has to ask the scripts something -- `DoAvoider` asks
   * four different things -- cannot queue the call the way `Animate`
   * does, because it needs the answer before it can decide what to do
   * next.  So the method is run to completion on the spot: `run` stops
   * as soon as the frame it pushed has returned, which makes this an
   * ordinary nested call rather than a new cycle.
   */
  private callMethod(o: RtObject, name: string, params: number[] = []): number {
    const sel = this.index.selectorId(name);
    if (sel < 0) return 0;
    const found = this.species.lookup(o.def, sel, o.scriptNo);
    if (!found) return 0;
    const pBase = this.stack.length;
    this.stack.push(params.length, ...params);
    this.run(found.script, o, found.offset,
             { steps: 20000, keep: true, nested: true, paramsBase: pBase });
    if (this.stack.length > pBase) this.stack.length = pBase;
    return this.acc;
  }

  /** An accumulator value that should name an object. */
  resolveTarget(f: Frame | null, ref: number): RtObject | null {
    if (ref === -1) return f?.obj ?? null;
    if (this.clones.has(ref)) return this.clones.get(ref)!;
    if (isRef(ref)) return this.objectAt(refScript(ref), refOffset(ref));
    return f ? this.objectAt(f.scriptNo, ref) : null;
  }

  /** Offset of exported procedure `index` in `scriptNo`, or -1. */
  exportOffset(scriptNo: number, index: number): number {
    const s = this.script(scriptNo);
    if (!s || index < 0 || index >= s.exports.length) return -1;
    const off = s.exports[index];
    return (off > 0 && off < s.data.length) ? off : -1;
  }

  private clones = new Map<number, RtObject>();
  /** Clones disposed during this cycle, swept at the start of the next. */
  private disposed = new Set<number>();
  /** What `GameIsRestarting` reports: 0 for no, 2 for a restart. */
  restarting = 0;
  /** Set by `RestartGame`, read by `run` so it gives up the cycle. */
  restartRequested = false;
  /**
   * Lists and nodes are kernel-owned structures a script only ever holds
   * a handle to, so they live here rather than in script memory.  Handles
   * share one descending allocator with clones: script 0x3FFF is a number
   * no game uses, which keeps every handle distinguishable from a real
   * object reference while still passing `isRef`.
   */
  private lists = new Map<number, { first: number; last: number }>();
  private nodes = new Map<number, { key: number; value: number;
                                    prev: number; next: number }>();
  private nextHandle = REF_TAG | (0x3FFF << 16) | 0xFFFF;
  private alloc() { return this.nextHandle--; }
  private rng = 1;

  /** Cached because Animate needs it on every frame. */
  private selDoit = -2;

  /**
   * Ticks since start, 1/60 s as the games assume.  Advanced by the
   * host once per displayed frame rather than by any kernel call, so
   * time passes for a game that is waiting without animating.
   */
  ticks = 0;
  /** Property reads that landed outside the object, for measurement. */
  oobProps = 0;
  /** Variable reads that landed outside their block, likewise. */
  oobVars = 0;
  private lastWait = 0;
  /**
   * Ticks a `Wait(0)` is held for -- the machine we claim to be.
   *
   * SCI0 games ask to wait zero and let the machine set the pace, and
   * they measure the answer: `SpeedTst` counts its own cycles for one
   * second and files the machine under 0, 1 or 2 at the boundaries 30
   * and 60 cycles a second.  Those three classes are the three machines
   * the games were sold for, so the boundaries name them: an 8088 XT,
   * a 286 AT, and a 386.
   *
   * Two ticks is thirty cycles a second, which is the bottom of the
   * middle class -- a 286 AT.  Three ticks was twenty, and every SCI0
   * game read that as slower than an XT: Camelot's title sequence then
   * turns off every picture transition and skips one of its credit
   * screens, because those are exactly the corners a machine that slow
   * was expected to cut.
   *
   * This is only ever consulted for `Wait(0)`.  In play the games name
   * their own interval -- Camelot waits 6 and 1, SQ3 waits 5 and 1 --
   * so the pace of the game itself does not pass through here.
   */
  minWait = 2;

  /** One tick is 1/60 s; the host advances it as frames are displayed. */
  advanceClock(n = 1) { this.ticks += n; }

  /**
   * Periodic sample of the innermost frame.  Where a run spends its
   * instructions is a different question from where it happened to stop,
   * and only a histogram answers the first one.
   */
  sampleEvery = 0;
  samples = new Map<string, number>();

  /** What Animate actually reached, for measurement. */
  animateStats = { calls: 0, doits: 0, max: 0, drawn: 0, names: new Set<string>() };
  /** Priority bands of the current picture. */
  picBands = [42, 53, 64, 74, 85, 95, 106, 116, 127, 138, 148, 159, 169, 180];
  /** True while a picture is laid in but not yet on the screen. */
  private pendingPic = false;
  picNotValid = 0;

  /** Show a picture that has been waiting, if one is. */
  private showPendingPic() {
    if (!this.pendingPic) return;
    this.pendingPic = false;
    this.picNotValid = 0;
    const [style, blackout] = this.pendingWipe;
    this.pendingWipe = ['none', false];
    this.screen.beginWipe(style, blackout, this.wallClock());
  }

  /** Where the wipes get their timing; a harness can hand over a clock. */
  wallClock: () => number = () => Date.now();
  private pendingWipe: [Wipe, boolean] = ['none', false];


  /** Walk a list to its values, cycle-guarded against damaged links. */
  private listValues(h: number): number[] {
    const l = this.lists.get(h);
    if (!l) return [];
    const out: number[] = [];
    const seen = new Set<number>();
    for (let n = l.first; n && !seen.has(n); ) {
      seen.add(n);
      const node = this.nodes.get(n);
      if (!node) break;
      out.push(node.value);
      n = node.next;
    }
    return out;
  }

  private unlink(listH: number, nodeH: number) {
    const l = this.lists.get(listH), n = this.nodes.get(nodeH);
    if (!l || !n) return;
    if (n.prev) { const p = this.nodes.get(n.prev); if (p) p.next = n.next; }
    else l.first = n.next;
    if (n.next) { const q = this.nodes.get(n.next); if (q) q.prev = n.prev; }
    else l.last = n.prev;
    n.prev = n.next = 0;
  }

  /**
   * Give every cast member its turn.
   *
   * Drawing is a renderer's business; what the scripts depend on is that
   * each member receives `doit:`, because that is what advances cyclers
   * and movers -- and a cycler reaching the end of its loop is what sends
   * `cue:`, which is how an SCI0 game steps a puzzle forward.
   */
  /**
   * The cast list `Animate` was last given.
   *
   * `Act::canBeHere` passes it to the kernel itself, but the step check
   * inside `DoBresen` has no such argument and needs the same list, so
   * it is kept here as the game hands it over.
   */
  private cast = 0;

  private animate(castH: number, f?: Frame): number {
    this.cast = castH;
    if (this.selDoit === -2) this.selDoit = this.index.selectorId('doit');
    if (this.selDoit < 0 || !f) return 0;
    const items: { target: RtObject; sel: number; params: number[] }[] = [];
    for (const v of this.listValues(castH)) {
      const o = this.resolveTarget(null, v);
      if (o) items.push({ target: o, sel: this.selDoit, params: [] });
    }
    this.animateStats.calls++;
    this.animateStats.doits += items.length;
    this.animateStats.max = Math.max(this.animateStats.max, items.length);
    for (const it of items) this.animateStats.names.add(it.target.name);
    if (items.length) f.kcalls = { items, i: 0, result: 0 };
    // Drawing happens now, from the properties as they stand.  The
    // doit: calls queued above run afterwards and take effect on the
    // next frame, which is the order the interpreter used: a cycler
    // advances a cel for the frame after the one being drawn.
    this.drawCast(castH);
    return 0;
  }

  /**
   * Composite every visible cast member over the picture.
   *
   * Sorted by priority so nearer sprites overwrite farther ones, and
   * each pixel still tested against the picture's own priority, which is
   * what puts an actor behind scenery rather than in front of it.
   */
  /** Everything about a view that decides what lands on the screen. */

  private drawCast(castH: number) {
    this.showPendingPic();
    /**
     * Everything in the cast, drawn or not, and what each will draw.
     *
     * Built before anything is put back, because what is put back
     * depends on who is still here: ScummVM's `update` walks the same
     * list to restore each stopped view's bits and save them again, so
     * a view keeps its pixels only once it has left the cast.
     */
    const inCast = new Set<RtObject>();
    const drawn: Array<{ o: RtObject; cel: Cel; left: number; top: number;
                        pri: number; y: number; z: number; order: number;
                        scenery: boolean }> = [];
    let order = 0;
    for (const v of this.listValues(castH)) {
      const o = this.resolveTarget(null, v);
      if (!o) continue;
      // Hidden or not, it is in the cast, and its bits are still owed
      // back -- that is how one credit makes way for the next.
      inCast.add(o);
      // signal bit 0x0008 is "hidden"; a view of -1 is nothing to draw.
      if (this.prop(o, 'signal') & 0x0008) continue;
      const cel = this.celOf(o);
      if (!cel) continue;
      const r = this.celRect(cel, this.prop(o, 'x'), this.prop(o, 'y'), this.prop(o, 'z'));
      // Unless the script has pinned it, an actor's priority follows its
      // feet down the screen, and the property is rewritten so scripts
      // reading it see the same band the drawing used.  Leaving a stale
      // value in place is what let the ego walk in front of scenery it
      // should have passed behind: Camelot's ego sat at priority 0 all
      // game while standing in band 7.
      let pri = this.prop(o, 'priority', -1);
      if (!(this.prop(o, 'signal') & SIGNAL_FIXED_PRIORITY)) {
        pri = this.priorityOf(s16(u16(this.prop(o, 'y'))));
        this.setProp(o, 'priority', pri);
      } else if (pri < 0 || pri > 15) pri = this.priorityOf(r.bottom - 1);
      /**
       * A view that has stopped moving is scenery.
       *
       * It is still drawn, but its rectangle is not handed to the
       * ordinary restore, so it survives the game dropping it from the
       * cast.  KQ4's title needs that: the three pieces of its "IV" fly
       * in, stop, and are dropped, and with their rectangles on the
       * restore list the next cycle took them away -- which is what the
       * opening question's window did on its way out, nine seconds
       * later, the numerals having sat there in the meantime only
       * because a modal dialog runs no cycles.
       *
       * What takes scenery off again is the game hiding it, which is
       * handled above.  The credits in the same intro are the case that
       * needs it: each one stops, is hidden, and is dropped, and
       * without the hiding half they pile up on one another.
       */
      const scenery = (u16(this.prop(o, 'signal')) & SIGNAL_STOP_UPDATE) !== 0;
      drawn.push({ o, cel, left: r.left, top: r.top, pri, scenery,
                   y: s16(u16(this.prop(o, 'y'))), z: s16(u16(this.prop(o, 'z'))),
                   order: order++ });
    }
    /**
     * Nearer the bottom of the screen is nearer the viewer, so that --
     * not priority -- is the order cast members are drawn in.
     *
     * Sorting by priority instead put anything sharing the ego's band
     * in front of it whenever it happened to come later in the cast:
     * Camelot's armour stand sits at y 108 and the ego walks to 110, so
     * the ego is in front of it, but both land in band 7 and the stand
     * was drawn last.  Ties fall back to z, then to the order the game
     * gave them, so two things at the same depth keep their arrangement.
     */
    this.screen.restoreCastAreas(o => o === null || inCast.has(o as RtObject));
    drawn.sort((a, b) => (a.y - b.y) || (a.z - b.z) || (a.order - b.order));
    // Each cel writes its priority as well as testing against it, so a
    // member drawn later cannot paint over one that is nearer the front.
    for (const d of drawn) {
      this.screen.castCovered(d.left, d.top, d.left + d.cel.width, d.top + d.cel.height,
                              d.scenery ? d.o : null);
      this.screen.drawCel(d.cel, d.left, d.top, d.pri, true, true);
    }
    this.animateStats.drawn += drawn.length;
  }

  /**
   * The step `DoBresen` takes on the cycles that are the actor's turn.
   */
  private bresenStep(mover: RtObject, client: RtObject) {
    const cx = s16(u16(this.prop(client, 'x')));
    const cy = s16(u16(this.prop(client, 'y')));
    const tx = s16(u16(this.prop(mover, 'x', cx)));
    const ty = s16(u16(this.prop(mover, 'y', cy)));
    this.setProp(mover, 'xLast', cx);
    this.setProp(mover, 'yLast', cy);
    const dx = s16(u16(this.prop(mover, 'dx')));
    const dy = s16(u16(this.prop(mover, 'dy')));
    const onX = this.prop(mover, 'b-xAxis') !== 0;
    // Arrived, or near enough that one more step would pass it.
    if (onX ? Math.abs(tx - cx) < Math.abs(dx) || dx === 0
            : Math.abs(ty - cy) < Math.abs(dy) || dy === 0) {
      this.setProp(client, 'x', tx);
      this.setProp(client, 'y', ty);
      return;
    }
    const i1 = s16(u16(this.prop(mover, 'b-i1')));
    const i2 = s16(u16(this.prop(mover, 'b-i2')));
    const incr = s16(u16(this.prop(mover, 'b-incr')));
    let di = s16(u16(this.prop(mover, 'b-di')));
    let nx = cx + dx, ny = cy + dy;
    if (di < 0) di += i1;
    else { di += i2; if (onX) ny += incr; else nx += incr; }
    /**
     * A step onto ground this actor may not stand on is taken back.
     *
     * The line state goes back with it, or the error term would carry
     * a step that never happened and the actor would drift off the
     * line.  The client is told by its signal, which is what
     * `Act::doit` and the avoiders read.
     *
     * A move out of a bad position is always allowed, so an actor put
     * somewhere illegal by a script can still get out.
     */
    if (!this.legalAt(client, nx, ny) && this.legalAt(client, cx, cy)) {
      this.setProp(client, 'signal',
        u16(this.prop(client, 'signal')) | SIGNAL_HIT_OBSTACLE);
      return;
    }
    this.setProp(client, 'signal',
      u16(this.prop(client, 'signal')) & ~SIGNAL_HIT_OBSTACLE);
    this.setProp(client, 'x', nx);
    this.setProp(client, 'y', ny);
    this.setProp(mover, 'b-di', di);
  }

  /** Sierra's y -> priority band. */
  priorityOf(y: number): number {
    const bands = this.picBands;
    return Math.max(1, Math.min(15, bands.filter(b => b <= y).length));
  }

  /**
   * The handful of kernel calls that shape control flow.  Everything
   * else is recorded and returns 0 -- graphics and sound cannot change
   * what a script decides, but object identity can.
   */
  kernel(id: number, args: number[], f?: Frame): number {
    const a0 = args[0] ?? 0, a1 = args[1] ?? 0;
    switch (this.index.kernelName(id)) {
      case 'ScriptID': return this.scriptID(args[0] ?? 0, args[1] ?? 0);
      case 'Clone': return this.cloneObject(args[0] ?? 0);
      /**
       * Marked for collection, not freed on the spot.
       *
       * SCI hands a disposed clone to the next garbage collection and
       * leaves it readable until then, and the scripts rely on it.
       * `Sound::play` disposes itself deliberately -- it sets a flag,
       * calls `dispose`, puts the flag back -- and then goes straight
       * on to `init` and to `DoSound` with the same `self`.  Freeing it
       * at the call left every one of those talking to a handle that
       * no longer named anything, so KQ4's intro music was created and
       * thrown away in the same breath and never played a note.
       */
      case 'DisposeClone': this.disposed.add(args[0] ?? 0); return 0;
      case 'IsObject': return this.resolveTarget(null, args[0] ?? 0) ? 1 : 0;
      case 'RespondsTo': {
        const o = this.resolveTarget(null, args[0] ?? 0);
        if (!o) return 0;
        const sel = args[1] ?? 0;
        return (o.indexOfSelector(sel) >= 0 ||
                this.species.lookup(o.def, sel, o.scriptNo) !== null) ? 1 : 0;
      }
      case 'Load': this.script(args[1] ?? 0); return args[1] ?? 0;

      // --- time -------------------------------------------------------
      /**
       * The clock, in the unit asked for.
       *
       * `GetTime()` is ticks since the game started; `GetTime(1)` is
       * the time of day in seconds.  Returning ticks for both made
       * every timed state run sixty times fast: `Script::doit` counts
       * its `seconds` down once per change in this value, so a scene
       * meant to hold for five seconds was gone in five cycles, and the
       * credits went by too quickly to read.
       */
      case 'GetTime': return (a0 === 1 ? Math.floor(this.ticks / 60) : this.ticks) & 0x7FFF;
      case 'Wait': {
        // Reached only once the wait is satisfied -- the interpreter loop
        // holds the instruction back until then -- so this reports how
        // long it actually took and opens the next interval.
        const elapsed = this.ticks - this.lastWait;
        const want = a0 > 0 ? a0 : this.minWait;
        // Advance by the interval rather than to the clock, so time
        // already earned is not thrown away: setting it to now means the
        // next wait always blocks and the game can never do more than
        // one cycle per frame, however fast the clock is running.  If it
        // has fallen a long way behind -- a slow frame, a background tab
        // -- give up the backlog instead of bursting through it.
        this.lastWait = elapsed > want * 8 ? this.ticks : this.lastWait + want;
        return elapsed;
      }

      // --- lists and nodes --------------------------------------------
      case 'NewList': { const h = this.alloc(); this.lists.set(h, { first: 0, last: 0 }); return h; }
      case 'DisposeList': {
        const l = this.lists.get(a0);
        if (l) { for (let n = l.first; n; ) { const nd = this.nodes.get(n); this.nodes.delete(n); n = nd?.next ?? 0; } }
        this.lists.delete(a0); return 0;
      }
      case 'NewNode': {   // NewNode(value, key)
        const h = this.alloc();
        this.nodes.set(h, { key: a1, value: a0, prev: 0, next: 0 });
        return h;
      }
      case 'FirstNode': return this.lists.get(a0)?.first ?? 0;
      case 'LastNode': return this.lists.get(a0)?.last ?? 0;
      case 'NextNode': return this.nodes.get(a0)?.next ?? 0;
      case 'PrevNode': return this.nodes.get(a0)?.prev ?? 0;
      case 'NodeValue': return this.nodes.get(a0)?.value ?? 0;
      case 'EmptyList': return this.lists.get(a0)?.first ? 0 : 1;
      case 'AddToFront': {
        const l = this.lists.get(a0), n = this.nodes.get(a1);
        if (!l || !n) return a1;
        n.prev = 0; n.next = l.first;
        if (l.first) { const q = this.nodes.get(l.first); if (q) q.prev = a1; } else l.last = a1;
        l.first = a1; return a1;
      }
      case 'AddToEnd': {
        const l = this.lists.get(a0), n = this.nodes.get(a1);
        if (!l || !n) return a1;
        n.next = 0; n.prev = l.last;
        if (l.last) { const p = this.nodes.get(l.last); if (p) p.next = a1; } else l.first = a1;
        l.last = a1; return a1;
      }
      case 'AddAfter': {   // AddAfter(list, node, newNode)
        const l = this.lists.get(a0), at = this.nodes.get(a1), nn = this.nodes.get(args[2] ?? 0);
        if (!l || !nn) return 0;
        if (!at) return this.kernel(id, [a0, args[2] ?? 0], f);
        nn.prev = a1; nn.next = at.next;
        if (at.next) { const q = this.nodes.get(at.next); if (q) q.prev = args[2] ?? 0; }
        else l.last = args[2] ?? 0;
        at.next = args[2] ?? 0; return args[2] ?? 0;
      }
      case 'FindKey': {
        for (let n = this.lists.get(a0)?.first ?? 0; n; ) {
          const nd = this.nodes.get(n); if (!nd) break;
          if (nd.key === a1) return n;
          n = nd.next;
        }
        return 0;
      }
      case 'DeleteKey': {
        for (let n = this.lists.get(a0)?.first ?? 0; n; ) {
          const nd = this.nodes.get(n); if (!nd) break;
          const next = nd.next;
          if (nd.key === a1) { this.unlink(a0, n); this.nodes.delete(n); return 1; }
          n = next;
        }
        return 0;
      }

      case 'Animate': return this.animate(a0, f);

      // --- picture and cels -------------------------------------------
      /**
       * Ask for a new picture.
       *
       * It is not painted here.  SCI marks the picture invalid and the
       * next `Animate` draws it together with the cast, which is what
       * keeps a room from appearing before the things standing in it --
       * and what lets a dialog open over the picture that is still on
       * screen.  Painting immediately blacked out Camelot's title the
       * moment its options menu was about to be drawn over it.
       */
      case 'DrawPic': {
        const d = this.game.tryData('pic', a0);
        if (!d) return 0;
        try {
          /**
           * Composed now, shown later.
           *
           * The third argument asks to add to the picture already
           * there; without it the screen is cleared first.  Only the
           * showing waits: the room's `init` runs before the next
           * `Animate` and asks the control plane where to put the ego,
           * and it has to be asking about the room it is entering.
           * Leaving the planes behind meant every answer came from the
           * room just left -- Camelot's map said the spot it had chosen
           * for Arthur was solid rock, and `Act::findPosn` spiralled
           * outward looking for somewhere better until it wandered off
           * the edge of the picture, which is how he arrived off screen
           * and walked in.
           */
          const pic = new Picture(d);
          this.screen.drawPic(pic, (args[2] ?? 0) === 0, false);
          // The saved pixels any window was holding belong to the
          // picture that has just gone; putting them back later would
          // paint the old room over the new one.
          this.windows.clear();
          this.picBands = pic.priorityBands ?? this.picBands;
          this.currentPic = a0;
          this.pendingPic = true;
          this.picNotValid = 1;
          /**
           * The low byte of the flags is how the picture is to arrive.
           *
           * Bit 15 is the blackout flag, and before SCI1 late it does
           * nothing: the translation table gives each old number both a
           * style and whether it blacks out, and ScummVM's `doit`
           * overwrites what the flag said with what the table says.
           * Those are the only versions here, so the table decides.
           */
          this.pendingWipe = wipeFor(u16(args[1] ?? 0));
        } catch { /* a picture that will not decode leaves the last one */ }
        return 0;
      }
      case 'DrawCel': {
        // DrawCel(view, loop, cel, x, y, priority)
        const v = this.view(a0);
        if (!v?.loopCount) return 0;
        // The loop and cel are clamped, as SCI clamps them.  Camelot
        // asks for cel 2 of a loop with two cels when it draws the
        // bottom right corner of a message panel; refusing to draw
        // simply leaves that corner off.
        const loop = v.loops[Math.max(0, Math.min(v.loopCount - 1, a1))];
        if (!loop?.length) return 0;
        const cel = loop[Math.max(0, Math.min(loop.length - 1, args[2] ?? 0))];
        if (!cel) return 0;
        // A priority of -1 means none was given: the cel is drawn
        // whatever the picture says.  Taking it as the lowest priority
        // instead skipped every pixel, which is why the ornament around
        // Camelot's message panels never appeared.
        const pri = s16(u16(args[5] ?? 15));
        this.screen.drawCel(cel, args[3] ?? 0, args[4] ?? 0, pri < 0 ? 15 : pri);
        return 0;
      }
      case 'AddToPic': {
        // Anything baked in belongs to the picture, so it has to be
        // there first.
        this.showPendingPic();
        // Bake the cast list handed in straight into the background.
        for (const val of this.listValues(a0)) {
          const o = this.resolveTarget(null, val);
          if (!o) continue;
          const cel = this.celOf(o);
          if (!cel) continue;
          const r = this.celRect(cel, this.prop(o, 'x'), this.prop(o, 'y'), this.prop(o, 'z'));
          let pri = this.prop(o, 'priority', -1);
          if (pri < 0 || pri > 15) pri = this.priorityOf(r.bottom - 1);
          this.screen.addToPic(cel, r.left, r.top, pri);
        }
        return 0;
      }
      /** Is a picture waiting to be drawn?  Setting it asks for a redraw. */
      case 'PicNotValid': {
        const was = this.picNotValid;
        if (args.length > 0) this.picNotValid = a0;
        return was;
      }
      /**
       * Drawing straight onto the planes.
       *
       * One kernel with many sub-functions, and the one place in SCI
       * where a rectangle is given as (top, left, bottom, right): the
       * documentation is explicit that the order is the opposite of
       * every other kernel.  Everything is relative to the current
       * port.
       *
       * Camelot's windows draw themselves with this -- `bordWindow`
       * fills its panel and then lays cels around the edge for the
       * ornament -- so a stub returning 0 left every message in the
       * game as text floating on the picture with nothing behind it.
       */
      case 'Graph': {
        const p = this.port;
        const y1 = p.y + s16(u16(a1)), x1 = p.x + s16(u16(args[2] ?? 0));
        const y2 = p.y + s16(u16(args[3] ?? 0)), x2 = p.x + s16(u16(args[4] ?? 0));
        switch (a0) {
          case 2: return 16;                       // grGET_COLOURS
          case 4: {                                // grDRAW_LINE
            this.screen.line(x1, y1, x2, y2, args[5] ?? 0);
            return 0;
          }
          /**
           * grSAVE_BOX, which is a script saying "I am about to cover
           * this, and I will put it back myself".
           *
           * So for as long as the box is held, something the script
           * drew is standing there and the cast must not paint over it.
           * Camelot's message panel is built exactly this way: the box
           * is saved, a grey panel and its border are drawn into it
           * with `Graph`, and a transparent window is opened over the
           * middle of it only to have a port to write the text in.
           * Protecting the window alone left the panel's border
           * unguarded -- 99,117-221,153 painted, 108,124-213,147
           * protected -- and Arthur walked through the ornament around
           * the edge of his own dialogue.
           */
          case 7: {                                // grSAVE_BOX
            const h = this.alloc();
            this.savedBits.set(h, this.screen.save(x1, y1, x2 + 1, y2 + 1));
            const area = { x0: x1, y0: y1, x1: x2 + 1, y1: y2 + 1 };
            this.savedAreas.set(h, area);
            this.screen.windows.push(area);
            this.screen.protectionChanged();
            return h;
          }
          case 8: {                                // grRESTORE_BOX
            const area = this.savedAreas.get(a1);
            if (area) {
              const at = this.screen.windows.indexOf(area);
              if (at >= 0) this.screen.windows.splice(at, 1);
              this.savedAreas.delete(a1);
              this.screen.protectionChanged();
            }
            const kept = this.savedBits.get(a1);
            if (kept) { this.screen.restoreRect(kept); this.savedBits.delete(a1); }
            return 0;
          }
          case 9: case 10: {                       // fill with the port's colours
            const colour = a0 === 9 ? (p.back ?? 15) : (p.pen ?? 0);
            this.screen.fill(x1, y1, x2 + 1, y2 + 1, colour & 0x0F);
            return 0;
          }
          case 11: {                               // grFILL_BOX
            const screens = args[5] ?? 1;
            const vis = s16(u16(args[6] ?? 0));
            const pri = s16(u16(args[7] ?? -1));
            const ctl = s16(u16(args[8] ?? -1));
            this.screen.fillPlanes(x1, y1, x2 + 1, y2 + 1, screens, vis, pri, ctl);
            return 0;
          }
          // Updating and redrawing are what a port with its own buffer
          // needs; everything here is already on the one screen.
          case 12: case 13: return 0;
          case 14: return 0;                       // grADJUST_PRIORITY
          default: return 0;
        }
      }
      // `SetPort` has a real implementation further down; listing it
      // here as a no-op shadowed it, because the first matching case
      // wins and a script switching ports was quietly ignored.
      case 'GetPort': return 0;

      // --- placement and movement --------------------------------------
      case 'BaseSetter': {
        // The base rectangle is the strip of floor a sprite stands on:
        // as wide as the cel, `yStep` deep, at its feet.  CanBeHere
        // tests this, not the whole sprite.
        const o = this.resolveTarget(null, a0);
        if (!o) return 0;
        const cel = this.celOf(o);
        if (!cel) return 0;
        const y = this.prop(o, 'y'), z = this.prop(o, 'z');
        const r = this.celRect(cel, this.prop(o, 'x'), y, z);
        const step = Math.max(1, this.prop(o, 'yStep', 2));
        this.setProp(o, 'brLeft', r.left);
        this.setProp(o, 'brRight', r.right);
        this.setProp(o, 'brBottom', y + 1);
        this.setProp(o, 'brTop', y + 1 - step);
        this.setProp(o, 'nsLeft', r.left);
        this.setProp(o, 'nsRight', r.right);
        this.setProp(o, 'nsTop', r.top);
        this.setProp(o, 'nsBottom', r.bottom);
        return 0;
      }
      /**
       * Set a mover up to walk its client to (x, y).
       *
       * A mover carries the destination; the thing that moves is its
       * `client`.  `Motion::init` calls this and `Motion::doit` then
       * calls `DoBresen` once a cycle, so without this the mover starts
       * with no idea how far it has to go -- which is why the ego stood
       * still with every part of the walking machinery apparently
       * running.
       */
      case 'InitBresen': {
        const mover = this.resolveTarget(null, a0);
        if (!mover) return 0;
        const client = this.resolveTarget(null, this.prop(mover, 'client'));
        if (!client) return 0;
        this.initBresen(mover, client, args.length > 1 ? (a1 || 1) : 1);
        return 0;
      }

      /**
       * One cycle of a mover: step its client along the line.
       *
       * The script decides arrival itself -- `Motion::doit` compares the
       * mover's x and y against the client's and calls `moveDone` when
       * they match -- so the last step has to land exactly on the
       * target rather than merely near it, or the walk never ends.
       */
      /**
       * One cycle of a mover: step its client along the line.
       *
       * `Motion::doit` calls `moveDone` only when the client's x and y
       * are exactly the mover's, and calls this otherwise, so the walk
       * ends only if the client lands on the target to the pixel.  That
       * is what the line state set up by `InitBresen` is for: each step
       * takes `dx`, `dy` along the dominant axis and the error term
       * decides when the other axis is nudged, so the last step arrives
       * rather than passing nearby.
       *
       * Once the remaining distance along that axis is shorter than one
       * step, the client is placed on the target outright.  Stopping a
       * step short instead leaves the two unequal for ever, and the
       * script goes on asking: a mover that cannot finish is a room
       * that never moves on.
       */
      /**
       * The avoider, which is what actually drives an actor's mover.
       *
       * `Act::doit` reads its `avoider` and, when there is one, calls
       * that and jumps straight past the branch that would have called
       * the mover.  So an actor with an avoider moves only if this
       * kernel ticks the mover for it.  Unimplemented, it returned
       * zero, and King's Quest IV's unicorn galloped on the spot: its
       * `MoveTo` was aimed correctly at x 350, off the right edge, and
       * `DoBresen` was called exactly once in a hundred and seventy
       * cycles of `Act::doit`.
       *
       * The shape is ScummVM's, written here from its description of
       * what the kernel reads, asks and returns.  Nothing is blocked
       * most of the time, and then the work is: step the mover, point
       * the client at where it is going, and answer -1.  When the
       * client is blocked, walk the compass from its own heading in
       * 45 degree steps, in the direction the avoider is turning, and
       * answer with the first heading it could actually stand in.
       */
      case 'DoAvoider': {
        const SIGNAL = -1;
        const avoider = this.resolveTarget(f ?? null, a0);
        if (!avoider) return SIGNAL;
        const client = this.resolveTarget(null, this.prop(avoider, 'client'));
        if (!client) return SIGNAL;
        if (!this.resolveTarget(null, this.prop(client, 'mover'))) return SIGNAL;

        const mv = this.resolveTarget(null, this.prop(client, 'mover'))!;
        this.callMethod(mv, 'doit');
        // The move may have finished and taken the mover with it.
        const mover = this.resolveTarget(null, this.prop(client, 'mover'));
        if (!mover) return SIGNAL;

        const blocked = this.callMethod(client, 'isBlocked') !== 0;
        let turn = s16(u16(this.prop(avoider, 'heading')));
        const cx = s16(u16(this.prop(client, 'x')));
        const cy = s16(u16(this.prop(client, 'y')));

        if (!blocked) {
          if (turn === SIGNAL) return SIGNAL;
          this.setProp(avoider, 'heading', SIGNAL);
          const mx = s16(u16(this.prop(mover, 'x', cx)));
          const my = s16(u16(this.prop(mover, 'y', cy)));
          const dx = mx - cx, dy = my - cy;
          const angle = (!dx && !dy) ? 0
            : ((Math.round(Math.atan2(dx, -dy) * 180 / Math.PI) % 360) + 360) % 360;
          const looper = this.resolveTarget(null, this.prop(client, 'looper'));
          if (looper) this.callMethod(looper, 'doit', [angle, client.handle]);
          else this.kernel(this.index.kernel.indexOf('DirLoop'), [client.handle, angle], f);
          return SIGNAL;
        }

        // Which way round the compass to try, once, at random.
        if (turn === SIGNAL) {
          this.rng = (this.rng * 1103515245 + 12345) & 0x7FFFFFFF;
          turn = (this.rng & 1) ? 45 : -45;
        }
        this.setProp(avoider, 'heading', turn);
        const xStep = s16(u16(this.prop(client, 'xStep', 1))) || 1;
        const yStep = s16(u16(this.prop(client, 'yStep', 1))) || 1;
        const from = Math.floor(s16(u16(this.prop(client, 'heading'))) / 45) * 45;
        for (let dir = from;;) {
          dir += turn;
          if (dir >= 360) dir -= 360;
          if (dir < 0) dir += 360;
          if (dir === from) break;                  // all the way round
          // Clockwise from north, which is how SCI counts headings.
          const east = dir > 0 && dir < 180 ? 1 : dir > 180 ? -1 : 0;
          const north = dir < 90 || dir > 270 ? 1 : dir > 90 && dir < 270 ? -1 : 0;
          this.setProp(client, 'x', cx + east * xStep);
          this.setProp(client, 'y', cy - north * yStep);
          if (this.callMethod(client, 'canBeHere')) return dir;
        }
        this.setProp(client, 'x', cx);
        this.setProp(client, 'y', cy);
        return SIGNAL;
      }

      /**
       * One step along the line, when this cycle is the actor's turn.
       *
       * The turn is what `b-moveCnt` counts, and it is the kernel's to
       * keep in SCI0 -- ScummVM calls that `kIncrementMoveCount`, which
       * is what every SCI0 and SCI01 game gets.  The count goes up each
       * call, and the step is taken only once it has passed the
       * client's `moveSpeed`, whereupon it goes back to nought.
       *
       * Nought is the part that matters beyond pacing.  `Motion::
       * triedToMove` is exactly `b-moveCnt == 0`, and `Act::isStopped`
       * answers "not stopped" whenever a mover says it did not try.
       * `Walk::doit` advances the walking cel only while the actor is
       * not stopped -- so a counter that never returns to nought means
       * a blocked actor is never stopped, and her legs go on walking
       * against the obstacle for as long as the key is held.  This used
       * to increment and never reset, and that is what Rosella did at
       * every wall.
       */
      case 'DoBresen': {
        const mover = this.resolveTarget(null, a0);
        if (!mover) return 0;
        const client = this.resolveTarget(null, this.prop(mover, 'client'));
        if (!client) return 0;
        let moveCnt = u16(this.prop(mover, 'b-moveCnt')) + 1;
        // No `moveSpeed` means nought, which is a step every cycle.
        const speed = s16(u16(this.prop(client, 'moveSpeed', 0)));
        if (speed < moveCnt) {
          moveCnt = 0;
          this.bresenStep(mover, client);
        }
        this.setProp(mover, 'b-moveCnt', moveCnt);
        return 0;
      }

      /**
       * Move an event between screen and window coordinates.
       *
       * A control's rectangle is relative to the window it sits in, so
       * a dialog converts the event before asking which control was
       * hit.  Passing the coordinates through unchanged -- which is
       * what this did, on the grounds that one port covered the whole
       * picture -- tests the click against the wrong rectangles, and
       * Camelot's menu could only be worked with the keyboard.
       */
      case 'GlobalToLocal': return this.shiftEvent(a0, -1);
      case 'LocalToGlobal': return this.shiftEvent(a0, 1);

      // --- input --------------------------------------------------------
      case 'HaveMouse': return 1;
      /**
       * SetCursor(resource [visible x y]).
       *
       * The second argument says whether the pointer is shown, not
       * where it is -- this used to read it as an x coordinate, so a
       * game hiding its cursor teleported the mouse to column 1
       * instead.  The position, when given at all, is the third and
       * fourth.
       *
       * Every game keeps its pointer in the same two resources: 999 is
       * the arrow, and 997 is the one it puts up while it is busy --
       * an hourglass in most of them, the Grail itself in Camelot.
       * Showing it is the whole point of the thing, so a player can
       * tell a game that is loading from one that has stopped.
       */
      case 'SetCursor': {
        this.screen.cursor = this.cursorOf(a0);
        this.screen.cursorVisible = args.length >= 2 ? a1 !== 0 : true;
        if (args.length >= 4) {
          this.mouseX = s16(u16(args[2] ?? 0));
          this.mouseY = s16(u16(args[3] ?? 0));
        }
        this.screen.cursorX = this.mouseX;
        this.screen.cursorY = this.mouseY;
        return 0;
      }
      case 'GetEvent': {
        const mask = a0;
        const ev = this.resolveTarget(null, a1);
        // A message from the parser is modal: the next thing the player
        // does takes it down, and the game does not get to act on it.
        if (this.parseMsg && !(mask & EV.peek)) {
          const j = this.events.findIndex(e => (e.type & (EV.keyboard | EV.mouseDown)) !== 0);
          if (j >= 0) {
            this.events.splice(j, 1);
            this.dismissParseMessage();
            if (ev) {
              this.setProp(ev, 'type', EV.null);
              this.setProp(ev, 'message', 0);
              this.setProp(ev, 'modifiers', 0);
              this.setProp(ev, 'x', this.mouseX);
              this.setProp(ev, 'y', this.mouseY);
            }
            return 0;
          }
        }
        const i = this.events.findIndex(e => (e.type & mask) !== 0);
        if (i < 0) {
          // An empty queue still has to say where the pointer is.  A
          // control being dragged polls this in a loop and asks whether
          // the pointer is still over it; a null event reporting 0,0
          // answers no, so Camelot's menu highlighted under the mouse
          // and then refused every click.
          if (ev) {
            this.setProp(ev, 'type', EV.null);
            this.setProp(ev, 'message', 0);
            this.setProp(ev, 'modifiers', 0);
            this.setProp(ev, 'x', this.mouseX);
            this.setProp(ev, 'y', this.mouseY);
          }
          return 0;
        }
        const e = this.events[i];
        if (!(mask & EV.peek)) this.events.splice(i, 1);
        if (ev) {
          this.setProp(ev, 'type', e.type);
          this.setProp(ev, 'message', e.message);
          this.setProp(ev, 'modifiers', e.modifiers);
          this.setProp(ev, 'x', e.x);
          this.setProp(ev, 'y', e.y);
        }
        return 1;
      }
      /**
       * The two halves of a restart, which KQ4 needs to start at all.
       *
       * Its intro is the attract loop: title, credits, Graham's collapse,
       * Rosella on Tamir with Genesta -- and then `RoomActions` state 32
       * calls `Game::restart`, which is `RestartGame`.  `KQ4::init` opens
       * by asking `GameIsRestarting`, and goes to room 25, the beach you
       * actually play, when the answer is yes; when it is no it goes to
       * the copy-protection room and the whole intro again.  So the only
       * way into the game is round this loop, and with `RestartGame`
       * doing nothing the intro ran to its end and stopped there with no
       * ego in the cast and `User.canInput` still false.  The player was
       * left looking at the beach unable to move.
       *
       * `GameIsRestarting` answers with the flag as it was, and a call
       * passing zero clears it -- which is what script 994 does once a
       * cycle, so the answer is yes only for the first read after the
       * restart.  That ordering is the whole mechanism: `play` runs
       * `init` before the cycle that clears it.
       */
      case 'GameIsRestarting': {
        const was = this.restarting;
        if (args.length && a0 === 0) this.restarting = 0;
        return was;
      }
      case 'RestartGame': {
        // The real interpreter shrinks the stack to its base and tells
        // the machine to give up as soon as it can; `run` sees this at
        // the top of the next step and stops, and the session builds
        // the game again from script 0.
        this.restartRequested = true;
        return 0;
      }
      case 'Joystick': return 0;

      // --- text and windows ---------------------------------------------
      case 'DrawStatus': {
        this.screen.drawStatus(this.font(0), this.stringAt(a0, f?.scriptNo));
        return 0;
      }
      /**
       * TextSize(rect, text, font, maxWidth).
       *
       * The result goes *into* the caller's rectangle, four words of it,
       * not into the return value.  A dialog sizes itself from what this
       * writes, so returning the measurement instead leaves every window
       * eight pixels wide with its text outside it.
       */
      case 'TextSize': {
        // Named `fnt`, not `f`: the frame is also called `f` here, and
        // shadowing it sent `stringAt` looking in script 0.
        const fnt = this.font(args[2] ?? 0) ?? this.font(0);
        const t = this.stringAt(a1, f?.scriptNo);
        /**
         * How wide a line may be.
         *
         * The kernel's own defaults, not the screen's: an unspecified
         * maximum wraps at 192, and -1 asks for one line however long
         * it turns out.  Wrapping at the full 320 instead is what gave
         * Camelot a message box 327 pixels wide, three pixels off the
         * left of a 320-pixel screen, with Merlin's answer stretched
         * across the whole picture on a single line.
         */
        const asked = s16(u16(args[3] ?? 0));
        const maxW = asked > 0 ? asked : asked < 0 ? 0x7FFF : TEXT_WIDTH;
        // Measured exactly as it will be drawn.  This used to wrap on
        // characters while the drawing wrapped on words, so a game sized
        // a panel for five lines and then six were written into it --
        // Camelot's message boxes had their last line sitting on the
        // border.
        const box = fnt ? this.textExtent(fnt, t, maxW) : { width: 0, height: 8 };
        this.writeWords(a0, [0, 0, box.height, box.width]);
        return 0;
      }


      // --- things that only need to not fail -----------------------------
      case 'Display': return this.display(args, f?.scriptNo);
      case 'GetFarText': {
        // GetFarText(resource, line, buffer) fills the buffer and returns
        // it, so the caller can go on using the address it passed in.
        const text = this.textLines(a0)[a1] ?? '';
        const buf = args[2] ?? 0;
        if (this.hasString(buf)) { this.setString(buf, text); return buf; }
        return this.makeString(text);
      }
      case 'Format': {
        // Format(dest, source, ...) writes into dest and returns it; the
        // source may be a string or a (resource, line) pair.
        let i = 1, src: string;
        if (this.hasString(a1) || isRef(a1)) { src = this.stringAt(a1, f?.scriptNo); i = 2; }
        else { src = this.textLines(a1)[args[2] ?? 0] ?? ''; i = 3; }
        const out = this.format(src, args.slice(i), f?.scriptNo);
        if (!a0) return this.makeString(out);
        this.setString(a0, out);
        return a0;
      }
      /**
       * The string kernels.
       *
       * A script's buffers are not addressable memory here, so the text
       * a pointer stands for is kept against the pointer itself and
       * `stringAt` looks there first.  That makes a copy into a buffer
       * readable afterwards wherever the pointer travels.
       *
       * `StrCpy` returning its destination unchanged, as it did, is not
       * a harmless stub: `Print` copies the text it was handed into a
       * buffer of its own before doing anything else, so every dialog
       * built that way came up empty.  Camelot's opening menu -- "See
       * the Intro", "Start New Game", "Restore Game" -- was an eight
       * pixel wide box because of it.
       */
      case 'StrLen': return this.stringAt(a0, f?.scriptNo).length;
      case 'StrCpy': {
        // A third argument caps the copy, and SCI passes a negative one
        // to mean "as many as fit", which is the same as no limit here.
        const n = args.length > 2 ? s16(u16(args[2])) : -1;
        const src = this.stringAt(a1, f?.scriptNo);
        this.setString(a0, n >= 0 ? src.slice(0, n) : src);
        return a0;
      }
      case 'StrCat': {
        this.setString(a0, this.stringAt(a0, f?.scriptNo) + this.stringAt(a1, f?.scriptNo));
        return a0;
      }
      case 'StrCmp': {
        let x = this.stringAt(a0, f?.scriptNo), y = this.stringAt(a1, f?.scriptNo);
        if (args.length > 2) { const n = args[2]; x = x.slice(0, n); y = y.slice(0, n); }
        return x < y ? -1 : x > y ? 1 : 0;
      }
      case 'StrEnd': {
        // The scripts use this to find where to append; the index of the
        // terminator is the closest thing to that pointer here.
        return this.stringAt(a0, f?.scriptNo).length;
      }
      case 'StrAt': {
        const i = Math.max(0, s16(u16(a1)));
        /**
         * A byte, and past the end of the string is still a byte.
         *
         * `DSelector::advance` asks for the character a whole entry
         * along -- thirty-six past the cursor -- to find out whether
         * there is another line below the one picked.  Reading that out
         * of the string the cursor points at answers nothing, because
         * the string stopped at its terminator thirty-odd bytes back,
         * and the saved-game list would not scroll past its first
         * entry.
         */
        if (isStackAddr(a0)) {
          const at = refOffset(a0) + i;
          const was = at < this.stackBytes.length ? this.stackBytes[at] : 0;
          if (args.length > 2 && at < this.stackBytes.length)
            this.stackBytes[at] = args[2] & 0xFF;
          return was;
        }
        const t = this.stringAt(a0, f?.scriptNo);
        const was = t.charCodeAt(i) || 0;
        // With a third argument it writes that character and reports
        // the one it replaced.
        if (args.length > 2) {
          const pad = t.length < i ? t + ' '.repeat(i - t.length) : t;
          this.setString(a0, pad.slice(0, i) + String.fromCharCode(args[2] & 0xFF) + pad.slice(i + 1));
        }
        return was;
      }

      /**
       * NewWindow(top, left, bottom, right, title, type, priority, fg, bg).
       *
       * The rectangle comes first and the games pass it in that order --
       * a window at (144, 156, 156, 164) is twelve rows tall and eight
       * wide, which is what an empty dialog is before its text sizes it.
       */
      case 'NewWindow': {
        const top = a0, left = a1, bottom = args[2] ?? a0, right = args[3] ?? a1;
        // NewWindow(top, left, bottom, right, title, style, priority, pen, back)
        const style = args[5] ?? 0;
        const pen = args[7] ?? 0;
        const bg = args[8] ?? 15;
        const x0 = Math.max(0, left - 1), y0 = Math.max(0, top - 1);
        const x1 = Math.min(WIDTH, right + 2), y1 = Math.min(HEIGHT, bottom + 2);
        /**
         * Only a window that paints something has anything to put back.
         *
         * `nwTRANSPARENT` draws no background, no border and no title,
         * and `nwNODRAW` draws nothing whatever, so neither covers a
         * pixel it would have to restore.  Saving for one of those and
         * restoring on dispose does real damage: it reinstates whatever
         * happened to be on the screen when the window opened, undoing
         * everything drawn there since.
         *
         * Camelot's message box is exactly that case.  The script
         * paints its own grey panel, brackets it with Graph's own save
         * and restore, and asks for a transparent window only to have a
         * port to write the text into.  Restoring on dispose put the
         * panel straight back over the picture the script had just
         * carefully restored, and it stayed there for good.
         */
        const draws = !(style & (WINDOW_TRANSPARENT | WINDOW_NODRAW));
        const saved = draws ? this.screen.save(x0, y0, x1, y1) : null;
        // A transparent window paints no background of its own and a
        // frameless one draws no border: Camelot's options box asks for
        // both (style 129) and draws its own ornament instead, so
        // filling it black hid the title art behind it and then the
        // white text on it as well.
        if (!(style & WINDOW_TRANSPARENT)) this.screen.fill(x0, y0, x1, y1, bg & 0x0F);
        if (!(style & (WINDOW_TRANSPARENT | WINDOW_NOFRAME))) this.screen.frame(x0, y0, x1, y1, 0);
        const port = { x: left, y: top, w: Math.max(1, right - left), h: Math.max(1, bottom - top),
                       pen: pen & 0x0F, back: bg & 0x0F, style };
        const h = this.alloc();
        // While it is open the picture is not painted back over it.
        const area = { x0, y0, x1, y1 };
        this.screen.windows.push(area);
        this.screen.protectionChanged();
        this.windows.set(h, { rect: saved, port, area });
        this.ports.push(port);
        return h;
      }
      case 'DisposeWindow': {
        const w = this.windows.get(a0);
        if (w) {
          const cover = this.screen.windows.indexOf(w.area);
          if (cover >= 0) { this.screen.windows.splice(cover, 1); this.screen.protectionChanged(); }
          if (w.rect) this.screen.restoreRect(w.rect);
          this.windows.delete(a0);
          const i = this.ports.lastIndexOf(w.port);
          if (i > 0) this.ports.splice(i, 1);
        }
        return 0;
      }
      case 'SetPort': {
        const w = this.windows.get(a0);
        if (w) { const i = this.ports.lastIndexOf(w.port); if (i < 0) this.ports.push(w.port); }
        else if (a0 === 0) this.ports.length = 1;
        return 0;
      }

      /**
       * DrawControl(control).
       *
       * The dialogs are built out of these: type 2 is a line of text,
       * type 3 an edit field, type 0 and 1 buttons.  Their rectangles are
       * relative to the window's port, and `state` bit 0 means selected,
       * which is drawn inverted.
       */
      case 'DrawControl': case 'HiliteControl': {
        const o = this.resolveTarget(null, a0);
        if (!o) return 0;
        const p = this.port;
        const x = p.x + this.prop(o, 'nsLeft');
        const y = p.y + this.prop(o, 'nsTop');
        const w = Math.max(0, this.prop(o, 'nsRight') - this.prop(o, 'nsLeft'));
        // SCI numbers its controls: 1 button, 2 text, 3 edit, 4 icon,
        // 6 list.  Zero is not one of them, but the games pass it for a
        // plain button and it has always been taken as one here.
        const type = this.prop(o, 'type');
        /**
         * "Change Directory" is not offered at all.
         *
         * There is nowhere else to put a saved game: they are the
         * page's, kept for the tab, and no directory the button could
         * name exists.  ScummVM disables it and leaves it sitting
         * there; here it is not drawn either, so the dialog is only the
         * choices that mean something.  Disabling still matters -- it
         * is what stops the keyboard from landing on a button that is
         * not on the screen.
         */
        if (o.name === 'changeDirI' || o.name === 'changeDirItem') {
          this.setProp(o, 'state', (this.prop(o, 'state') | 4) & ~1);
          return 0;
        }
        const state = this.prop(o, 'state');
        const text = this.stringAt(this.prop(o, 'text'), o.scriptNo);
        const font = this.font(this.prop(o, 'font')) ?? this.font(0);
        // Bit 0 says the control is enabled; bit 3 says it is the one
        // highlighted.  The games are explicit about it: Camelot's
        // three options all carry state 3 and the one under the cursor
        // is redrawn as 11.  Reading bit 0 as "selected" drew every
        // button inverted, so all three looked picked at once.
        const selected = (state & 8) !== 0;
        // Controls take their colours from the window they sit in; a
        // dialog on a black background writes in white, and drawing
        // everything in black made Camelot's menu invisible on its own
        // backdrop.
        const pen = p.pen ?? 0, back = p.back ?? 15;
        if (type === 0 || type === 1) {
          const bottom = p.y + this.prop(o, 'nsBottom');
          // Erase before drawing, whichever state it is in.  A button
          // is redrawn as the highlight moves off it, and filling only
          // when selected left the inverted block behind: the option
          // stayed a solid white slab with white text on it and its
          // frame lost in the fill.
          //
          // The frame sits one pixel outside the control's own
          // rectangle.  Two pixels wider and it runs into the button
          // below, which turned Camelot's three options into a block of
          // white bars.
          this.screen.fill(x - 1, y - 1, x + w + 1, bottom + 1, selected ? pen : back);
          this.screen.frame(x - 1, y - 1, x + w + 1, bottom + 1, pen);
          if (font && text) this.screen.text(font, text, x + 1, y, selected ? back : pen);
        } else if (type === CONTROL_ICON) {
          /**
           * A picture in the dialog, next to the words.
           *
           * Camelot's death and quit box is one: `myIcon` in script 128
           * is a `DCIcon` carrying view 999 and a `cycleSpeed`, so it is
           * not a still picture but a little animation running beside
           * the question.  The cycling is the game's own -- `DCIcon`
           * makes a cycler in `init` and its `cycle` advances the cel
           * and calls `draw` again when it changes -- so all that was
           * missing was somewhere for that draw to land.  Falling
           * through to the text branch, an icon has no text and nothing
           * appeared at all.
           */
          const cel = this.celOf(o);
          if (cel) {
            // Drawn over the dialog rather than into the scene, so it
            // is not tested against the picture's priority.
            this.screen.drawCel(cel, x, y, 15, false, false);
            // Bit 5 of the style asks for a border around it.
            if (state & 0x20)
              this.screen.frame(x, y, x + cel.width, y + cel.height, pen);
          }
        } else if (type === 3) {
          this.drawEditField(o, x, y, w, font, pen, back);
        } else if (type === CONTROL_LIST) {
          this.drawList(o, x, y, w, p.y + this.prop(o, 'nsBottom'), font, pen, back);
        } else if (font && text) {
          this.drawText(font, text, x, y, pen, Math.max(8, w || (WIDTH - x)));
        }
        return 0;
      }

      /**
       * EditControl(control, event).
       *
       * Typing into a text field.  Only an edit control has anything to
       * do here, and only a keyboard event: the caller hands every
       * control in the dialog the same event, so the ones that do not
       * apply have to leave it alone rather than claim it.
       *
       * The text lives in the buffer a `lea` handle names, which is what
       * the control's `text` property holds, so editing means rewriting
       * that buffer -- not the property.
       */
      case 'EditControl': {
        const ctl = this.resolveTarget(null, a0);
        const ev = this.resolveTarget(null, a1);
        if (!ctl || !ev) return 0;
        if (this.prop(ctl, 'type') !== 3) return 0;
        if (this.prop(ev, 'type') !== EV.keyboard) return 0;
        const buf = this.prop(ctl, 'text');
        if (!this.hasString(buf)) return 0;
        const max = this.prop(ctl, 'max', 40);
        let text = this.stringAt(buf, ctl.scriptNo);
        let cur = Math.max(0, Math.min(text.length, this.prop(ctl, 'cursor', text.length)));
        const key = this.prop(ev, 'message');
        let handled = true;
        if (key === 8) {                                  // backspace
          if (cur > 0) { text = text.slice(0, cur - 1) + text.slice(cur); cur--; }
        } else if (key === 0x4B00) { if (cur > 0) cur--; }        // left
        else if (key === 0x4D00) { if (cur < text.length) cur++; } // right
        else if (key === 0x4700) { cur = 0; }                      // home
        else if (key === 0x4F00) { cur = text.length; }            // end
        else if (key === 0x5300) { text = text.slice(0, cur) + text.slice(cur + 1); }
        else if (key >= 32 && key < 256) {
          if (text.length < max && this.fitsInField(ctl, text, key)) {
            text = text.slice(0, cur) + String.fromCharCode(key) + text.slice(cur);
            cur++;
          }
        } else handled = false;                 // enter and the rest are the dialog's
        if (!handled) return 0;
        this.setString(buf, text);
        this.setProp(ctl, 'cursor', cur);
        this.setProp(ev, 'claimed', 1);
        // Redrawing is part of this kernel's job, not a later call's.
        // Editing the buffer alone leaves the field showing whatever it
        // showed when the dialog opened: the whole phrase is typed, the
        // parser receives it, and the screen still shows the first
        // letter, which looks exactly like typing doing nothing.
        this.redrawControl(ctl);
        return 1;
      }

      /**
       * The sound driver.
       *
       * A `Sound` object carries the resource number and is its own
       * handle; the driver reports back by way of the object's `signal`
       * property, which is what `Sound::check` polls.  Subops the games
       * never call, and queries with nothing to answer from, fall
       * through to zero.
       */
      /**
       * Turn a direction key into a direction event.
       *
       * This is the whole of keyboard walking.  `User::handleEvent`
       * hands its event here and then acts on the *type* it comes back
       * with, so a machine that does not implement this leaves the
       * event a plain keystroke: the ego never moves, and the key falls
       * through to whatever else is listening.  Returning 0 is not a
       * harmless stub -- it is the difference between a game that can
       * be played and one that only looks like it.
       */
      case 'MapKeyToDir': {
        const ev = this.resolveTarget(null, a0);
        if (!ev) return 0;
        if (this.prop(ev, 'type') !== EV.keyboard) return 0;
        const dir = KEY_DIRECTION[u16(this.prop(ev, 'message'))];
        if (dir === undefined) return 0;
        this.setProp(ev, 'type', EV.direction);
        this.setProp(ev, 'message', dir);
        return 1;
      }

      case 'DoSound': {
        const verb = this.sounds.verb(a0);
        if (!verb) return 0;
        // Every verb but the global ones names the game's own `Sound`
        // object, which doubles as the driver's handle for the piece.
        const obj = a1 ? this.resolveTarget(null, a1) : null;
        const num = obj ? this.prop(obj, 'number') : 0;
        switch (verb) {
          case 'init':
            if (obj) { this.sounds.init(a1, num); this.setProp(obj, 'handle', a1); }
            return 0;
          case 'play':
            if (obj) {
              // `loop` counts repeats; -1 is what a script sets to mean
              // "keep going", and anything else plays the piece once.
              this.sounds.play(a1, num, s16(u16(this.prop(obj, 'loop'))) === -1, this.ticks);
              this.setProp(obj, 'handle', a1);
              this.setProp(obj, 'signal', 0);
            }
            return 0;
          case 'dispose': this.sounds.dispose(a1); return 0;
          case 'stop':
            this.sounds.stop(a1);
            if (obj) this.setProp(obj, 'signal', 0);
            return 0;
          // SCI0's `Sound::pause` passes its own argument straight
          // through, so there it is a flag and everything stops
          // together; SCI01 names the piece and passes the flag second.
          case 'pause':
            if (this.sounds.sci01) this.sounds.pause(a1, !!(args[2] ?? 1));
            else this.sounds.pause(0, !!a1);
            return 0;
          /**
           * Sound on or off.
           *
           * The argument is whether sound is *on*, not whether it is
           * muted, and reading this back is the same question -- which
           * is how a menu bar draws a tick beside "Sound".  Taking it
           * the other way round silenced Camelot from its intro
           * onwards: `Intro::init` turns sound on with `DoSound(4, 1)`
           * and then starts the music, so reading that as "mute" left
           * every piece after the title screen playing at zero gain.
           */
          case 'soundOn':
            if (args.length > 1) this.sounds.setMuted(!a1);
            return this.sounds.muted ? 0 : 1;
          case 'masterVolume':
            if (args.length > 1) this.sounds.setMasterVolume(a1);
            return this.sounds.masterVolume;
          case 'fade': this.sounds.fade(a1); return 0;
          // Nine melodic voices, which is what the chip has.
          case 'getPolyphony': return 9;
          case 'stopAll': this.sounds.stopAll(); return 0;
          // `check` is polled every cycle; the answer a script wants is
          // carried on the object's own `signal`, which `pumpSounds`
          // writes, so there is nothing to return here.
          case 'check': case 'update': case 'hold':
          case 'sendMidi': case 'restore': case 'resume':
            return 0;
        }
        return 0;
      }

      /**
       * Declare a menu.  The title goes on the bar and the items are
       * one colon-separated string; `parseItems` does the marking up.
       */
      case 'AddMenu':
        this.menu.add(this.stringAt(a0, f?.scriptNo), this.stringAt(a1, f?.scriptNo));
        return 0;

      /** Show or hide the bar. */
      case 'DrawMenuBar': {
        if (a0) {
          this.menu.drawBar(this.screen, this.font(0));
          this.screen.statusVisible = true;
        } else this.screen.statusVisible = false;
        return 0;
      }

      /**
       * Change one item: its `Said` spec, its text, its shortcut or
       * whether it can be chosen.  A game disables what does not apply
       * to where the player is standing, so this is called constantly.
       */
      case 'SetMenu': {
        // Several (subFunction, value) pairs may follow the item.
        for (let i = 1; i + 1 < args.length + 1 && i < args.length; i += 2) {
          const it = this.menu.item(a0);
          if (!it) break;
          const v = args[i + 1] ?? 0;
          if (args[i] === SM.said) it.said = v;
          else if (args[i] === SM.text) it.text = this.stringAt(v, f?.scriptNo);
          else if (args[i] === SM.key) it.key = v;
          else if (args[i] === SM.enable) it.enabled = v !== 0;
        }
        return 0;
      }

      case 'GetMenu': {
        const it = this.menu.item(a0);
        if (!it) return 0;
        if (a1 === SM.said) return it.said;
        if (a1 === SM.text) return this.makeString(it.text);
        if (a1 === SM.key) return it.key;
        if (a1 === SM.enable) return it.enabled ? 1 : 0;
        return 0;
      }

      /**
       * Read a line the player typed.
       *
       * Returns whether every word was understood.  A game that gets no
       * for an answer says so itself -- `wordFail` names the word back
       * to the player -- so answering 0 for everything, as this did,
       * left pressing Return doing nothing at all.
       */
      case 'Parse': {
        const text = this.stringAt(a0, f?.scriptNo);
        const ev = this.resolveTarget(null, a1);
        this.parser.event = a1;
        const unknown = this.parser.parse(text);
        if (ev) {
          this.setProp(ev, 'claimed', 0);
          if (!unknown) this.setProp(ev, 'type', EV.said);
        }
        /**
         * Answering a line the parser could not read.
         *
         * The script's whole response to a failed `Parse` is to return,
         * so unless the interpreter says something nothing is said at
         * all -- and a word the game has never heard of looks exactly
         * like a keyboard that has stopped working.  "remove suit of
         * armor" is one: Camelot knows "armor", "armour" and "mail",
         * but not "suit".
         *
         * The two failures are different and the games word them
         * differently.  A word outside the vocabulary is named back, so
         * the player can try another; a line of words it knows but
         * cannot fit to the grammar is not.
         */
        if (unknown) {
          const t = this.systemMessage(/understand.*%s/i, PMachine.UNKNOWN_WORD);
          this.showParseMessage(t.replace(/%s/, unknown));
          return 0;
        }
        if (!this.parser.parse_) {
          this.showParseMessage(this.systemMessage(/proper sentence/i, PMachine.BAD_SENTENCE));
          return 0;
        }
        return 1;
      }

      /**
       * Does the line match this pattern?
       *
       * A match claims the event the parse was given, so nothing else
       * acts on the same words, and spends the line -- the games ask
       * their specific patterns before their general ones and rely on
       * only the first answering.
       */
      case 'Said': {
        const spec = this.saidSpec(a0);
        if (!spec) return 0;
        const r = this.parser.match(spec);
        if (r.matched && r.claim) {
          const ev = this.resolveTarget(null, this.parser.event);
          if (ev) this.setProp(ev, 'claimed', 1);
        }
        return r.matched ? 1 : 0;
      }

      /**
       * Unload a script, so that loading it again starts it over.
       *
       * A no-op here, and that quietly broke every region KQ4 shares
       * between rooms.  `Rm::setRegions` asks each region whether it is
       * `initialized` and only calls `init` when it is not; `init` is
       * what puts the region into the list the game cycles.  SCI's
       * answer is fresh each room because leaving one unloads its
       * scripts and `ScriptID` loads them again with their properties
       * back at the values the resource carries.  Keeping the objects
       * for ever left `initialized` at 1 from the room before, so
       * `waterReg` was never added again and its `doit` -- which is
       * what looks at the ground under the ego and swaps her to a
       * wading view -- stopped running after the first room that used
       * it.  Rosella walked on top of the creek.
       *
       * A script that is running stays until it is not, which is what
       * the lock count does in the real interpreter.
       */
      /**
       * Saving and restoring, which the scripts drive.
       *
       * The two answer the opposite way round, and ScummVM is the
       * authority for that: `kSaveGame` gives back true when it worked
       * and `kRestoreGame` gives back *nothing* when it worked, true
       * being the failure.  The slots themselves belong to whoever is
       * hosting the game -- the page keeps them for the session -- so
       * they are handed over rather than written here.
       *
       * A restore does what a restart does: give up what is running,
       * build the machine again, put the saved state into it and
       * re-enter `play`, with `GameIsRestarting` saying restore rather
       * than restart so `Game::replay` takes it from there.
       */
      case 'SaveGame': {
        const name = this.stringAt(args[2] ?? 0, f?.scriptNo);
        const slot = this.slotToWrite(s16(u16(args[1] ?? 0)));
        if (slot < 0) return 0;
        return this.putSave?.(slot, this.snapshot(), name) ? 1 : 0;
      }
      case 'RestoreGame': {
        const snap = this.getSave?.(slotOf(s16(u16(args[1] ?? 0)))) ?? null;
        if (!snap) return 1;                       // true is the failure
        this.restoreRequested = snap;
        this.restartRequested = true;
        return 0;
      }
      case 'CheckSaveGame':
        return this.getSave?.(slotOf(s16(u16(args[1] ?? 0)))) ? 1 : 0;
      /**
       * The catalogue the game's own save dialog is built on.
       *
       * `GetSaveFiles(gameId, names, ids)` fills two buffers the script
       * hands over: twenty fixed thirty-six byte slots of text, ended by
       * an empty one, and a word per entry saying which saved game it
       * is.  Both are addresses into the caller's temps, so the writing
       * is into the stack -- see `STACK_SPACE`.
       */
      case 'GetSaveFiles': {
        const list = (this.listSaves?.() ?? []).slice(0, MAX_SAVES);
        const names = args[1] ?? 0, ids = args[2] ?? 0;
        for (let i = 0; i < list.length; i++)
          this.setString(names + i * SAVE_NAME_LEN, list[i].name.slice(0, SAVE_NAME_LEN - 1));
        this.setString(names + list.length * SAVE_NAME_LEN, '');
        this.writeWords(ids, list.map(e => e.slot + SAVE_ID_BASE));
        return list.length;
      }
      /**
       * How much room there is, which there always is.
       *
       * Early SCI0 asks with the path alone and wants a yes; later
       * builds pass a sub-function, and ScummVM's answers are the ones
       * used here: nought for the size a save would take, thirty-two
       * megabytes of free space, and yes there is room.  Answering zero
       * to all of it is what put King's Quest IV's dialog on the
       * "this disk can hold no more saved games" path with the
       * catalogue it had just been given still unread.
       */
      case 'CheckFreeSpace': {
        const sub = args.length > 1 ? s16(u16(args[1])) : 2;
        return sub === 0 ? 0 : sub === 1 ? 0x7FFF : 1;
      }
      /**
       * Which drive the game is on, which is none.
       *
       * The scripts use it to decide whether to offer "Change
       * Directory" and whether the saved games might be on a floppy
       * that has to be swapped.  One device, never removable, and every
       * path is the same path.
       */
      case 'DeviceInfo': {
        const mode = s16(u16(a0));
        if (mode === 0) { this.setString(args[2] ?? 0, '/'); return this.acc; }
        if (mode === 1) { this.setString(a1, '/'); return this.acc; }
        if (mode === 2)
          return this.stringAt(a1, f?.scriptNo) === this.stringAt(args[2] ?? 0, f?.scriptNo) ? 1 : 0;
        if (mode === 3) return 0;                  // never a floppy
        // 5 and 6 name the catalogue and a save's file, which the games
        // then delete by hand; there are no files, so nothing is named.
        if (mode === 5 || mode === 6) { this.setString(a1, ''); return this.acc; }
        return 0;
      }
      case 'ValidPath': return 1;
      case 'DisposeScript': {
        const n = u16(a0);
        if (this.frames.some(fr => fr.scriptNo === n)) this.unloadPending.add(n);
        else this.unloadScript(n);
        return args.length > 1 ? a1 : this.acc;
      }
      case 'GetCWD': { this.setString(a0, '/'); return a0; }
      case 'GetSaveDir': {
        if (!this.saveDir) this.saveDir = this.makeString('/');
        return this.saveDir;
      }
      case 'FlushResources': case 'MemoryInfo':
      case 'SetSynonyms':
      case 'FileIO':
      case 'FOpen': case 'FClose': case 'FGets': case 'FPuts':
        return 0;

      // --- geometry ---------------------------------------------------
      // SCI angles are degrees clockwise from north, which is why sine
      // drives x and cosine drives y (and y grows downward, so it is
      // negated).  Movers and `findPosn` are built entirely out of these.
      case 'SinMult': return Math.round(Math.sin(a0 * Math.PI / 180) * a1);
      case 'CosMult': return Math.round(Math.cos(a0 * Math.PI / 180) * a1);
      case 'SinDiv': { const d = Math.sin(a0 * Math.PI / 180); return d ? Math.round(a1 / d) : 0; }
      case 'CosDiv': { const d = Math.cos(a0 * Math.PI / 180); return d ? Math.round(a1 / d) : 0; }
      case 'Abs': return Math.abs(s16(u16(a0)));
      case 'Sqrt': return Math.round(Math.sqrt(Math.abs(a0)));
      case 'GetDistance': {
        const dx = a0 - (args[2] ?? 0), dy = a1 - (args[3] ?? 0);
        return Math.round(Math.sqrt(dx * dx + dy * dy));
      }
      case 'GetAngle': {
        // (x1,y1) -> (x2,y2), degrees clockwise from north.
        const dx = (args[2] ?? 0) - a0, dy = (args[3] ?? 0) - a1;
        if (!dx && !dy) return 0;
        return ((Math.round(Math.atan2(dx, -dy) * 180 / Math.PI) % 360) + 360) % 360;
      }

      /**
       * No obstacle model yet -- but the stub has to say "yes".  `CanBeHere`
       * returning 0 means "blocked", and `Act::findPosn` loops until it
       * finds somewhere it can stand, so a blanket "no" is an infinite
       * search that stops a room ever finishing its init.
       */
      /**
       * May this actor stand where it now is?
       *
       * The control plane is a map of the floor: every pixel carries a
       * colour, and an actor's `illegalBits` names the colours it may
       * not stand on.  Only the base rectangle is tested, which is the
       * actor's feet -- a head passing in front of a wall is ordinary,
       * standing inside one is not.
       *
       * `Act::doit` asks this after every step and calls `findPosn` to
       * nudge the actor back when the answer is no, so answering yes to
       * everything, as this used to, is what let the ego walk through
       * scenery and off the edge of the picture.
       */
      case 'CanBeHere': {
        const o = this.resolveTarget(null, a0);
        if (!o) return 1;
        const left = s16(u16(this.prop(o, 'brLeft')));
        const right = s16(u16(this.prop(o, 'brRight')));
        const top = s16(u16(this.prop(o, 'brTop')));
        const bottom = s16(u16(this.prop(o, 'brBottom')));
        // `Act::canBeHere` hands over the cast so that actors can stand
        // in each other's way.  Everything else this has to weigh --
        // including the edge of the picture, which is not a wall -- is
        // in `standable`, which the walk itself also asks.
        return this.standable(o, left, top, right, bottom, a1 || this.cast) ? 1 : 0;
      }

      /**
       * Which control colours lie under an actor, or under a rectangle.
       *
       * Rooms use it to notice the ego reaching a doorway or stepping
       * into water, so returning 0 meant none of that ever fired.
       */
      case 'OnControl': {
        /**
         * Two forms, and the short one was missing.
         *
         * `OnControl(map, left, top, right, bottom)` reports on a
         * rectangle -- an actor's base, which is what almost every call
         * wants.  `OnControl(map, x, y)` asks about a single point, and
         * falling through to the actor branch with an x coordinate
         * where an object was expected resolved nothing and answered
         * "no control colours here" every time.
         *
         * Camelot's map is driven entirely by that short form: `rm1`
         * reads the control colour under Arthur to work out which part
         * of Britain he is standing on.  Always hearing 0 back, it
         * decided he had wandered out of the region he started in and
         * walked him back to where he began -- so the map let him move
         * a few steps in any direction and then pulled him home again.
         *
         * The first argument selects the map; only the control one is
         * ever asked for here.
         */
        /**
         * The map is optional, and the count is what says it is there.
         *
         * A rectangle is four numbers and a point is two, so an odd
         * count means the first one chooses the map and an even one
         * means the coordinates start at the front.  Taking it as
         * always present read KQ4's `Act::onControl` -- which passes
         * its base rectangle bare -- as a question about the point
         * (top, right): a y of 277 on a screen 190 high, clamped away
         * to nothing, answered "no control colours here" every time.
         *
         * `findPosn` will not put an actor down until that answer is
         * something, so the fairies in the Tamir scene were refused
         * every spot it tried.  The search widens as it fails, and it
         * failed for ever: the actor was thrown further and further
         * out until it left the room, and the scene never went on.
         */
        const mapped = (args.length & 1) === 1;
        const at = mapped ? 1 : 0;
        const n = args.length - at;
        if (n >= 4) {
          const x1 = s16(u16(args[at])), y1 = s16(u16(args[at + 1]));
          const x2 = s16(u16(args[at + 2])), y2 = s16(u16(args[at + 3]));
          return this.controlBits(Math.min(x1, x2), Math.min(y1, y2),
                                  Math.max(x1, x2) + 1, Math.max(y1, y2) + 1);
        }
        if (n >= 2) {
          const x = s16(u16(args[at])), y = s16(u16(args[at + 1]));
          return this.controlBits(x, y, x + 1, y + 1);
        }
        // A few scripts hand over the actor itself instead of numbers.
        const o = this.resolveTarget(null, args[at] ?? 0);
        if (!o) return 0;
        return this.controlBits(s16(u16(this.prop(o, 'brLeft'))), s16(u16(this.prop(o, 'brTop'))),
                                s16(u16(this.prop(o, 'brRight'))), s16(u16(this.prop(o, 'brBottom'))));
      }

      /**
       * Point an actor the way it is heading.
       *
       * A view holds a loop per facing, and this picks the one matching
       * a heading in degrees clockwise from north.  Without it an actor
       * keeps whatever loop it last had, which is why the ego walked in
       * every direction still facing one way.
       *
       * The four-loop convention is the views' own: 0 faces right, 1
       * left, 2 towards the viewer, 3 away.  A view with fewer loops
       * than that has no back or front to turn to, so the heading only
       * chooses between left and right.
       */
      case 'DirLoop': {
        const o = this.resolveTarget(null, a0);
        if (!o) return 0;
        // An object that does not turn keeps the loop the script gave
        // it, whichever way the mover is taking it.
        if (this.prop(o, 'signal') & SIGNAL_NO_TURN) return 0;
        const angle = ((s16(u16(a1)) % 360) + 360) % 360;
        // Early SCI0 used a narrower arc for front and back; the later
        // interpreter widened both to a full quadrant.
        const arc = this.index.selectorShift === 1 ? 30 : 45;
        let loop = -1;
        if (angle > 360 - arc || angle < arc) loop = 3;            // away
        else if (angle > 180 - arc && angle < 180 + arc) loop = 2; // towards
        if (loop < 0) loop = angle >= 180 ? 1 : 0;                 // left : right
        else if ((this.view(this.prop(o, 'view'))?.loopCount ?? 0) < 4) return 0;
        this.setProp(o, 'loop', loop);
        return 0;
      }

      /**
       * Refresh an actor's "now seen" rectangle from its current cel.
       *
       * Rooms test against this rectangle, so leaving it behind after a
       * turn makes an actor respond to the shape it used to be.
       */
      case 'SetNowSeen': {
        const o = this.resolveTarget(null, a0);
        if (!o) return 0;
        const cel = this.celOf(o);
        if (!cel) return 0;
        const r = this.celRect(cel, this.prop(o, 'x'), this.prop(o, 'y'), this.prop(o, 'z'));
        this.setProp(o, 'nsLeft', r.left);
        this.setProp(o, 'nsTop', r.top);
        this.setProp(o, 'nsRight', r.right);
        this.setProp(o, 'nsBottom', r.bottom);
        return 0;
      }

      // --- view metrics -----------------------------------------------
      // A cycler decides it has finished by comparing `cel` against the
      // loop's last cel, so `NumCels` returning 0 means no cycle ever
      // completes, no `cue:` is ever sent, and every animation sits on
      // its first frame.  These come straight out of the view decoder.
      case 'NumLoops': return this.view(this.propOf(a0, 'view'))?.loopCount ?? 0;
      case 'NumCels': {
        const v = this.view(this.propOf(a0, 'view'));
        return v?.loops[this.propOf(a0, 'loop')]?.length ?? 0;
      }
      case 'CelWide': return this.view(a0)?.loops[a1]?.[args[2] ?? 0]?.width ?? 0;
      case 'CelHigh': return this.view(a0)?.loops[a1]?.[args[2] ?? 0]?.height ?? 0;
      case 'Random': {
        const lo = args[0] ?? 0, hi = args[1] ?? 0;
        this.rng = (this.rng * 1103515245 + 12345) & 0x7FFFFFFF;   // deterministic
        return hi > lo ? lo + (this.rng % (hi - lo + 1)) : lo;
      }
      default: return 0;
    }
  }

  /**
   * Decoded views, with each cel's pixels as the resource had them.
   *
   * The pristine copy is what makes merging reversible: `unditherCel`
   * rewrites a cel in place, and the merges depend on both the setting
   * and the room, either of which can change under a view that is
   * already loaded.
   */
  private views = new Map<number, { view: View | null; plain: Uint8Array[]; stamp: number }>();

  /**
   * Decoded view resource, cached; null when absent or malformed.
   *
   * A cel arrives as 4-bit colour indices, and where the artist drew a
   * chequerboard to fake a colour the EGA did not have, that is what a
   * modern display shows.  The picture behind it is already blended --
   * its plane stores the pair per pixel, so `rgb` just mixes them -- so
   * leaving cels alone put dithered sprites in front of smooth
   * backgrounds.  Merging a cel's pairs the same way needs the pattern
   * found first, and then cross-checked against the background: a
   * combination is merged only if the picture dithered with it too,
   * which is what keeps deliberate chequerboard texture intact.
   *
   * A merged pixel holds a pair byte rather than an index, which `blit`
   * already passes through untouched.
   */
  private view(n: number): View | null {
    let e = this.views.get(n);
    if (!e) {
      const d = n >= 0 ? this.game.tryData('view', n) : null;
      let v: View | null = null;
      if (d) { try { v = new View(d); } catch { v = null; } }
      const plain = v ? v.loops.flat().map(c => c.pixels.slice()) : [];
      e = { view: v, plain, stamp: -1 };
      this.views.set(n, e);
    }
    // Which background the merges were decided against, or 0 for a view
    // left as the artist drew it.
    const want = this.screen.undither ? this.screen.picEpoch + 1 : 0;
    if (e.view && e.stamp !== want) {
      const cels = e.view.loops.flat();
      cels.forEach((c, i) => { c.pixels.set(e!.plain[i]); });
      if (this.screen.undither) {
        const hist = this.screen.backgroundHistogram();
        for (const c of cels) unditherCel(c, hist);
      }
      e.stamp = want;
    }
    return e?.view ?? null;
  }

  /** Read a named property off an object handle, or -1. */
  private propOf(ref: number, name: string): number {
    const o = this.resolveTarget(null, ref);
    if (!o) return -1;
    const i = o.indexOfSelector(this.index.selectorId(name));
    return i < 0 ? -1 : o.props[i];
  }

  /** Selector id by name, cached; -1 when the game has no such selector. */
  sel(name: string): number {
    let v = this.selCache.get(name);
    if (v === undefined) { v = this.index.selectorId(name); this.selCache.set(name, v); }
    return v;
  }

  /** Read a named property of an object, or a default. */
  prop(o: RtObject, name: string, dflt = 0): number {
    const i = o.indexOfSelector(this.sel(name));
    return i < 0 ? dflt : o.props[i];
  }
  /**
   * A property is a word, and arithmetic on one wraps.
   *
   * Handles do not: this machine keeps object and buffer references in
   * properties too, and those are tagged above the sixteenth bit, so
   * they are stored whole.  Everything else is sign-extended from the
   * low word, as the games' own arithmetic does.
   */
  static word(v: number) { return (v > 0 && (v & REF_TAG)) ? v : ((v << 16) >> 16); }

  setProp(o: RtObject, name: string, v: number) {
    const i = o.indexOfSelector(this.sel(name));
    if (i >= 0) o.props[i] = PMachine.word(v);
  }

  /** Decoded font, cached. */
  font(n: number): Font | null {
    if (!this.fonts.has(n)) {
      const d = this.game.tryData('font', n);
      let f: Font | null = null;
      if (d) { try { f = new Font(d); } catch { f = null; } }
      this.fonts.set(n, f);
    }
    return this.fonts.get(n) ?? null;
  }

  /**
   * Where a cel lands and how big it is.
   *
   * (x, y) is the sprite's bottom centre, displaceX signed and negated
   * on a mirrored loop, displaceY unsigned -- the same convention the
   * static scene compositor uses, because it is the same convention the
   * interpreter used.
   */
  celRect(cel: Cel, x: number, y: number, z: number) {
    const dx = cel.mirrored ? -cel.xShift : cel.xShift;
    const dy = cel.yShift >= 0 ? cel.yShift : cel.yShift + 256;
    const left = x + dx - (cel.width >> 1);
    const bottom = y + dy - z + 1;
    return { left, top: bottom - cel.height, right: left + cel.width, bottom };
  }

  /** The cel an object's view/loop/cel properties name. */
  celOf(o: RtObject): Cel | null {
    const v = this.view(this.prop(o, 'view', -1));
    if (!v) return null;
    const loop = v.loops[this.prop(o, 'loop')] ?? v.loops[0];
    if (!loop?.length) return null;
    return loop[Math.min(Math.max(0, this.prop(o, 'cel')), loop.length - 1)] ?? null;
  }

  /**
   * Display(text, attributes...).
   *
   * The text is either a string the kernel or a script owns, or a
   * (resource, line) pair -- the games use both, so which one it is has
   * to be decided from the value rather than assumed.
   *
   * After it come attribute codes, read from the calls the games
   * actually make: 100 takes a coordinate pair, 101 a font, 102 and 103
   * the two colours, 105 a width; 107 and 121 take nothing.  An
   * unrecognised code stops the scan rather than guessing a length,
   * because guessing wrong reads the next code as a value and turns the
   * rest of the arguments into nonsense.
   */
  /**
   * Write text straight onto the picture.
   *
   * The parameter codes are SCI0's own, from `sci.sh`: 100 dsCOORD
   * (x, y), 101 dsALIGN, 102 dsCOLOR, 103 dsBACKGROUND (-1 for none),
   * 104 dsDISABLED, 105 dsFONT, 106 dsWIDTH, 107 dsSAVEPIXELS (no
   * parameter, returns a handle) and 108 dsRESTOREPIXELS.
   *
   * Reading 105 as the width, as this did, is not a small slip: the
   * intro writes each line twice at the same place, once in an outline
   * font and once in a face font over it.  Taking both font numbers as
   * widths drew one font twice, wrapped at two different points, which
   * is why the narration came out doubled and unreadable.  Ignoring 103
   * is why the lines that should sit in a panel had nothing behind them.
   */
  private display(args: number[], fromScript = 0): number {
    let i = 0;
    let text: string;
    if (this.hasString(args[0]) || isRef(args[0])) { text = this.stringAt(args[0], fromScript); i = 1; }
    else { text = this.textLines(args[0])[args[1] ?? 0] ?? ''; i = 2; }

    let x = 0, y = 0, fg = 15, bg = -1, align = 0, width = 0, haveXY = false, save = false;
    for (; i < args.length;) {
      const code = args[i++];
      if (code === 100) { x = s16(u16(args[i++])); y = s16(u16(args[i++])); haveXY = true; }
      else if (code === 101) { align = s16(u16(args[i++])); }
      else if (code === 102) { fg = args[i++] & 0x0F; }
      else if (code === 103) { bg = s16(u16(args[i++])); }
      else if (code === 104) { i++; }                    // grey text
      else if (code === 105) { this.dsFont = args[i++]; }
      else if (code === 106) { width = s16(u16(args[i++])); }
      else if (code === 107) { save = true; }
      else if (code === 108) {
        // Put back what was saved; everything else is ignored.
        const h = args[i++];
        const kept = this.savedBits.get(h);
        if (kept) { this.screen.restoreRect(kept); this.savedBits.delete(h); }
        this.screen.protectionChanged();
        return 0;
      }
      else break;
    }
    if (!text) return 0;
    const font = this.font(this.dsFont) ?? this.font(0);
    if (!font) return 0;
    if (!haveXY) { x = 0; y = 0; }
    const p = this.port;
    const w = width > 0 ? Math.min(width, WIDTH - p.x - x) : WIDTH - p.x - x;
    const px = p.x + x, py = p.y + y;

    // Measure before drawing: the area is needed for the background,
    // for saving under, and for putting the picture back later.  The
    // box is what the text actually fills, not the width it was allowed
    // -- a background painted out to the edge of the port put a black
    // band across the border of Camelot's title screen, where the
    // copyright line is only as wide as the words in it.
    const box = this.textExtent(font, text, w);
    const rect = { x0: px, y0: py,
                   x1: Math.min(WIDTH, px + box.width), y1: Math.min(HEIGHT, py + box.height) };
    let handle = 0;
    if (save) {
      handle = this.alloc();
      this.savedBits.set(handle, this.screen.save(rect.x0, rect.y0, rect.x1, rect.y1));
    }
    // Text written in an earlier cycle where this line is going goes
    // first, so the line replaces it rather than printing over it.
    this.screen.clearStaleOverlays(rect);
    if (bg >= 0) this.screen.fill(rect.x0, rect.y0, rect.x1, rect.y1, bg & 0x0F);
    this.drawText(font, text, px, py, fg, w, align);
    // Keep it: the next cycle restores the picture, and anything written
    // on top of it would go with it.
    this.screen.overlays.push({ ...rect, epoch: this.screen.epoch });
    this.screen.protectionChanged();
    return handle;
  }

  /** Pixels a script asked to be saved, by handle. */
  private savedBits = new Map<number, { x0: number; y0: number; w: number; h: number; buf: Uint8Array }>();
  /**
   * Where each saved box is, so the cast can be kept off it.
   *
   * Held by identity rather than by value: the same rectangle is the
   * entry in the screen's protected list, so removing it on restore is
   * a lookup rather than a search for something that compares equal.
   */
  private savedAreas = new Map<number, { x0: number; y0: number; x1: number; y1: number }>();

  /** How much room `text` takes when wrapped to `width`. */
  private textExtent(font: Font, text: string, width: number): { width: number; height: number } {
    const lineHeight = Math.max(8, font.lineHeight);
    let lines = 0, widest = 0;
    const done = (line: string) => { widest = Math.max(widest, this.measure(font, line)); lines++; };
    for (const para of text.split('\n')) {
      let line = '';
      for (const word of para.split(' ')) {
        const next = line ? `${line} ${word}` : word;
        if (line && this.measure(font, next) > width) { done(line); line = word; } else line = next;
      }
      done(line);
    }
    return { width: Math.min(width, widest), height: lines * lineHeight };
  }

  private measure(font: Font, s: string): number {
    let w = 0;
    for (const ch of s) w += font.chars[ch.charCodeAt(0)]?.width ?? 0;
    return w;
  }

  /** Draw text, wrapping on spaces inside the given width. */
  /** Draw wrapped text; returns the y just past the last line. */
  private drawText(font: Font, text: string, x: number, y: number,
                   colour: number, width: number, align = 0): number {
    const lineHeight = Math.max(8, font.lineHeight);
    let cy = y;
    /** Place one line according to the alignment asked for. */
    const put = (line: string) => {
      const w = this.measure(font, line);
      const lx = align > 0 ? x + Math.max(0, (width - w) >> 1)
               : align < 0 ? x + Math.max(0, width - w)
               : x;
      this.screen.text(font, line, lx, cy, colour);
      cy += lineHeight;
    };
    for (const para of text.split('\n')) {
      let line = '';
      for (const word of para.split(' ')) {
        const next = line ? `${line} ${word}` : word;
        if (line && this.measure(font, next) > width) { put(line); line = word; }
        else line = next;
      }
      put(line);
    }
    return cy;
  }

  /** The printf subset the scripts use. */
  /**
   * The printf subset the scripts use.
   *
   * The width and alignment are not decoration: SQ3 lays its status
   * line out by padding the score to a fixed width and right-aligning
   * the title, so parsing the specifier and then ignoring it ran the
   * two together as "Score: 0 of 738Space Quest III".
   */
  private format(src: string, args: number[], fromScript = 0): string {
    let out = '', ai = 0;
    for (let i = 0; i < src.length; i++) {
      if (src[i] !== '%') { out += src[i]; continue; }
      let j = i + 1;
      let left = false;
      // SCI writes `%-10s` for left-aligned and `%10s` for right.
      while (j < src.length && (src[j] === '-' || src[j] === '+' || src[j] === ' ')) {
        if (src[j] === '-') left = true;
        j++;
      }
      let width = 0;
      while (j < src.length && src[j] >= '0' && src[j] <= '9') width = width * 10 + (src.charCodeAt(j++) - 48);
      let prec = -1;
      if (src[j] === '.') {
        j++; prec = 0;
        while (j < src.length && src[j] >= '0' && src[j] <= '9') prec = prec * 10 + (src.charCodeAt(j++) - 48);
      }
      const kind = src[j];
      const v = args[ai++];
      let piece: string | null = null;
      if (kind === 'd') piece = String(s16(u16(v ?? 0)));
      else if (kind === 'u') piece = String(u16(v ?? 0));
      else if (kind === 's') piece = this.stringAt(v ?? 0, fromScript);
      else if (kind === 'c') piece = String.fromCharCode(v ?? 32);
      else if (kind === 'x') piece = u16(v ?? 0).toString(16);
      else if (kind === '%') { out += '%'; ai--; i = j; continue; }
      else { out += src.slice(i, j + 1); ai--; i = j; continue; }
      if (prec >= 0 && kind === 's') piece = piece.slice(0, prec);
      if (piece.length < width) {
        const pad = ' '.repeat(width - piece.length);
        piece = left ? piece + pad : pad + piece;
      }
      out += piece;
      i = j;
    }
    return out;
  }

  private get port() { return this.ports[this.ports.length - 1]; }

  /**
   * The parser's own messages, and the box they appear in.
   *
   * When the parser cannot make anything of a line, the reply comes
   * from the interpreter rather than from the game: the script's whole
   * response to a failed `Parse` is to return, so nothing at all was
   * said back and a mistyped word looked exactly like a dead keyboard.
   *
   * The wording is the games' own.  Resource text.994 is the system
   * message table, and the later SCI0 games carry the parser's lines in
   * it -- "I don't understand \"%s\"." for a word the vocabulary has
   * not got, and "That doesn't appear to be a proper sentence." for one
   * it knows every word of but cannot fit to the grammar.  The earliest
   * ones, Camelot among them, ship a shorter table and kept those two
   * inside the interpreter, so they are spelled out here as a fallback.
   * They are matched by content rather than by index, because the index
   * moves with the size of the table.
   */
  private static readonly UNKNOWN_WORD = 'I don\'t understand "%s".';
  private static readonly BAD_SENTENCE = "That doesn't appear to be a proper sentence.";

  /** A message on the screen, and the pixels it is covering. */
  private parseMsg: { rect: { x0: number; y0: number; w: number; h: number; buf: Uint8Array };
                      area: { x0: number; y0: number; x1: number; y1: number } } | null = null;

  /** The system message whose text looks like `like`, or `fallback`. */
  private systemMessage(like: RegExp, fallback: string): string {
    for (const l of this.textLines(994)) if (like.test(l)) return l;
    return fallback;
  }

  /**
   * Put a message on the screen and hold it there.
   *
   * Centred, black on white with a frame, and registered the way a
   * window is so the picture is not painted back over it.  It stays
   * until the player presses or clicks something -- `GetEvent` spends
   * that event on taking it down rather than passing it to the game,
   * which is what a modal box does.
   */
  private showParseMessage(text: string) {
    this.dismissParseMessage();
    const font = this.font(0);
    if (!font) return;
    const box = this.textExtent(font, text, TEXT_WIDTH);
    const w = Math.min(WIDTH - 8, box.width + 10), h = box.height + 10;
    const x0 = Math.max(0, (WIDTH - w) >> 1), y0 = Math.max(0, (HEIGHT - h) >> 1);
    const x1 = Math.min(WIDTH, x0 + w), y1 = Math.min(HEIGHT, y0 + h);
    const area = { x0, y0, x1, y1 };
    const rect = this.screen.save(x0, y0, x1, y1);
    this.screen.fill(x0, y0, x1, y1, 15);
    this.screen.frame(x0, y0, x1, y1, 0);
    this.drawText(font, text, x0 + 5, y0 + 5, 0, w - 10, 1);
    this.screen.windows.push(area);
    this.screen.protectionChanged();
    this.parseMsg = { rect, area };
  }

  /** Take the message down, if one is up.  True if there was one. */
  private dismissParseMessage(): boolean {
    const m = this.parseMsg;
    if (!m) return false;
    const i = this.screen.windows.indexOf(m.area);
    if (i >= 0) { this.screen.windows.splice(i, 1); this.screen.protectionChanged(); }
    this.screen.restoreRect(m.rect);
    this.parseMsg = null;
    return true;
  }

  /** Decoded cursor resource, cached; null when absent or malformed. */
  private cursorOf(n: number): Cursor | null {
    if (!this.cursors.has(n)) {
      const d = n >= 0 ? this.game.tryData('cursor', n) : null;
      let c: Cursor | null = null;
      if (d) { try { c = new Cursor(d); } catch { c = null; } }
      this.cursors.set(n, c);
    }
    return this.cursors.get(n) ?? null;
  }

  /** Lines of a text resource, cached. */
  textLines(n: number): string[] {
    let l = this.textRes.get(n);
    if (!l) {
      const d = this.game.tryData('text', n);
      l = d ? textStrings(d) : [];
      this.textRes.set(n, l);
    }
    return l;
  }

  /**
   * Write words into an array a script owns.
   *
   * Several kernels report by filling a caller-supplied rectangle rather
   * than by returning, so the machine has to be able to write back into
   * script memory, not only read from it.
   */
  writeWords(ref: number, values: number[]) {
    // A `lea` handle names a run of variables, not a place in script
    // memory, and that is where a rectangle filled by the kernel has to
    // land -- the script reads it straight back out of those variables.
    const slot = this.slotArray(ref);
    if (slot) {
      for (let i = 0; i < values.length; i++) {
        const at = slot.index + i;
        if (at < 0) continue;
        if (Array.isArray(slot.arr)) {
          while (slot.arr.length <= at) slot.arr.push(0);
          slot.arr[at] = values[i];
        } else if (at < slot.arr.length) slot.arr[at] = values[i];
      }
      return;
    }
    const scriptNo = isRef(ref) ? refScript(ref) : 0;
    const off = isRef(ref) ? refOffset(ref) : ref;
    const sc = this.script(scriptNo);
    if (!sc || off <= 0) return;
    for (let i = 0; i < values.length; i++) {
      const p = off + i * 2;
      if (p + 1 >= sc.data.length) return;
      sc.data[p] = values[i] & 0xFF;
      sc.data[p + 1] = (values[i] >> 8) & 0xFF;
    }
  }

  private buffers = new Map<string, number>();
  /**
   * The bytes behind the stack, which is what a string in a temp is.
   *
   * Shadowing rather than packing into `this.stack` keeps the word view
   * the opcodes use and the byte view the string kernels use out of
   * each other's way: no script writes a slot both ways.
   */
  private stackBytes = new Uint8Array(MAX_STACK * 2);

  /** True when text written at this handle belongs in the stack's bytes. */
  private stackText(h: number) { return isStackAddr(h); }

  /** Write a NUL-terminated string wherever a handle points. */
  setString(h: number, text: string) {
    if (!this.stackText(h)) { this.strings.set(h, text); return; }
    let p = refOffset(h);
    for (let i = 0; i < text.length && p < this.stackBytes.length - 1; i++)
      this.stackBytes[p++] = text.charCodeAt(i) & 0xFF;
    if (p < this.stackBytes.length) this.stackBytes[p] = 0;
  }

  /** Whether a handle names somewhere text can be written. */
  hasString(h: number) { return this.strings.has(h) || this.stackText(h); }

  /** Clear the bytes a frame's temps occupy, so no older text shows through. */
  private clearStackText(from: number, words: number) {
    const at = from * 2, end = Math.min(this.stackBytes.length, at + words * 2);
    if (at < end) this.stackBytes.fill(0, at, end);
  }
  /** Which variable slot a `lea` handle stands for. */
  private bufferSlot = new Map<number, {
    kind: number; index: number; script: number;
    /** For a temp or a parameter, the frame the slot belongs to. */
    frame?: Frame;
  }>();

  /**
   * A stable stand-in for the address of one variable slot.
   *
   * Globals and locals are identified by index, so one handle can serve
   * every use of that slot.  A temp or a parameter lives on the value
   * stack at an address that depends on the frame, so those are keyed by
   * where they actually are -- the `Print` dialogs measure themselves
   * into a temporary rectangle, and a handle that forgot which frame it
   * came from would write into somebody else's.
   */
  bufferFor(kind: number, index: number, script: number, f: Frame): number {
    const stack = kind === 2 || kind === 3;
    const at = kind === 2 ? f.tempsBase + index
             : kind === 3 ? f.paramsBase + index : index;
    // A stack slot's address is its address; everything else gets a
    // stand-in handle, one per slot, allocated the first time it is asked
    // for.
    if (stack) {
      this.bufferSlot.set(stackAddr(at), { kind, index: at, script, frame: f });
      return stackAddr(at);
    }
    const key = `${kind}:${index}:${script}`;
    let h = this.buffers.get(key);
    if (h === undefined) {
      h = this.alloc();
      this.buffers.set(key, h);
      this.strings.set(h, '');
    }
    // A stack address only means anything while the frame that owns it
    // is still running.  Recording the frame is what stops a handle kept
    // in some object's property from later writing into whatever method
    // happens to occupy those slots now -- which corrupts its temps, and
    // a method whose temp is its return value then returns nonsense.
    this.bufferSlot.set(h, { kind, index: at, script });
    return h;
  }

  /** Where a `lea` handle points, if anywhere writable. */
  private slotArray(h: number):
      { arr: Int32Array | number[]; index: number } | null {
    const slot = this.bufferSlot.get(h);
    if (!slot) {
      // An address the scripts worked out themselves -- the saved-game
      // catalogue is one buffer walked in thirty-six byte strides -- so
      // there is no `lea` on record for it.  It is still the stack.
      if (!isStackAddr(h)) return null;
      const word = refOffset(h) >> 1;
      return word < this.stack.length ? { arr: this.stack, index: word } : null;
    }
    if (slot.kind === 0) return { arr: this.globals, index: slot.index };
    if (slot.kind === 1) return { arr: this.localsOf(slot.script), index: slot.index };
    // The frame has returned, so those slots are somebody else's now.
    if (!slot.frame || !this.frames.includes(slot.frame)) return null;
    return { arr: this.stack, index: slot.index };
  }

  /** Put a string on the kernel's heap and return its handle. */
  makeString(s: string): number {
    const h = this.alloc();
    this.strings.set(h, s);
    return h;
  }

  /**
   * Read a NUL-terminated string a script pointed at.
   *
   * A tagged reference names its script; a bare offset is assumed to sit
   * in script 0, which is where the shared strings live.
   */
  /**
   * The text a script is pointing at.
   *
   * A bare offset carries no script with it -- `lofsa` only tags a
   * reference when the target is an object -- so the script it came
   * from has to be supplied.  Assuming script 0 reads the same offset
   * out of the wrong resource: `DEdit::setSize` measures the string "M"
   * to size the parser's input box, and reading script 0 at that offset
   * gave "0.001" instead, five characters wide, which the script then
   * multiplied by the field's 45-character limit into a box 1252 pixels
   * across.
   */
  stringAt(ref: number, fromScript = 0): string {
    const made = this.strings.get(ref);
    if (made !== undefined) return made;
    if (isStackAddr(ref)) {
      let out = '';
      for (let p = refOffset(ref); p < this.stackBytes.length && this.stackBytes[p]; p++)
        out += String.fromCharCode(this.stackBytes[p]);
      return out;
    }
    const scriptNo = isRef(ref) ? refScript(ref) : fromScript;
    const off = isRef(ref) ? refOffset(ref) : ref;
    const sc = this.script(scriptNo);
    if (!sc || off <= 0 || off >= sc.data.length) return '';
    let out = '';
    for (let p = off; p < sc.data.length && sc.data[p]; p++) out += String.fromCharCode(sc.data[p]);
    return out;
  }

  /** A script's exported object, which is how scripts reach each other. */
  scriptID(scriptNo: number, index: number): number {
    const off = this.exportOffset(scriptNo, index);
    if (off < 0) return 0;
    const s = this.script(scriptNo);
    if (!s) return 0;
    // An export may point at the object header or at its property array.
    for (const def of s.objects)
      if (def.offset === off || def.offset + 12 === off) {
        this.instantiate(scriptNo, def);
        return makeRef(scriptNo, def.offset + 12);
      }
    return makeRef(scriptNo, off);
  }

  cloneObject(ref: number): number {
    const src = this.resolveTarget(null, ref);
    if (!src) return 0;
    const copy = new RtObject(src.def, src.scriptNo, src.propSelectors);
    copy.props = Int32Array.from(src.props);
    const handle = this.alloc();
    copy.handle = handle;
    this.clones.set(handle, copy);
    return handle;
  }
}
