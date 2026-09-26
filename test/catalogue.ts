/**
 * The game's own saved-game dialog.
 *
 * King's Quest IV would not save at all: its dialog reported "this
 * directory/disk can hold no more saved games" and offered to replace
 * one of the none it had.  The dialog is built out of kernels that were
 * all stubbed to zero, and zero is the wrong answer to every one of
 * them.  `CheckFreeSpace` saying there is no room is what puts the
 * script on that path; `GetSaveFiles` is what fills the list of games
 * that already exist; `DeviceInfo` is what decides whether a floppy
 * needs swapping first.  ScummVM's answers are the ones used -- always
 * room, never a floppy, one device, every path the same path.
 *
 * The catalogue itself is a buffer of twenty fixed thirty-six byte
 * entries in the caller's temps, and the scripts walk it by pointer
 * arithmetic, so it also needs a `lea` on a temp to name a real address
 * -- see `STACK_SPACE` -- and `StrAt` to read a byte past the end of
 * the string it lands on, which is how `DSelector::advance` finds out
 * whether there is another line below the one picked.
 *
 * And a restored game re-enters the game object at `replay`, not at
 * `play`.  ScummVM does exactly that, and the scripts are written for
 * it: `Game::play` calls `init`, and `KQ4::init` asks
 * `GameIsRestarting` and sends the player to room 25 whenever the
 * answer is anything but no.  Restoring through `play` therefore put
 * Rosella on the beach whatever room the save was made in.
 */
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { Game, type ResourceSource } from '../src/resources.ts';
import { Index } from '../src/script.ts';
import { Session } from '../src/vm/session.ts';
import { ROOT } from './games.ts';

function nodeSource(dir: string): ResourceSource {
  const files = readdirSync(dir);
  return { names: () => files, read: (n: string) => new Uint8Array(readFileSync(join(dir, n))) };
}

let failed = 0, checked = 0;
const check = (ok: boolean, msg: string) => {
  checked++; if (!ok) failed++;
  console.log(`  ${ok ? 'ok  ' : 'FAIL'}  ${msg}`);
};

const F5 = 0x3F00, F7 = 0x4100, ENTER = 0x0D, DOWN = 0x5000, BACKSPACE = 8;

const g = new Game(nodeSource(join(ROOT, 'KQ4')));
const idx = new Index(g);
const s = new Session(g, idx);
let clock = 0;
s.now = () => clock;

interface Machine {
  kernel(id: number, a: number[], f?: unknown): number;
  resolveTarget(a: null, v: number): unknown;
  prop(o: unknown, n: string, d?: number): number;
  stringAt(p: number, sc?: number): string;
  objects?: Map<number, unknown>;
}
const vm = () => s.vm as unknown as Machine;

/** Every control the dialogs draw, in order, and the text that reaches the screen. */
let controls: Array<{ name: string; type: number; text: string; at: number; from: number }> = [];
let drawn: string[] = [];
const DRAW_CONTROL = idx.kernel.indexOf('DrawControl');
let watched: unknown = null;
const watch = () => {
  const m = vm();
  if (m === watched) return;
  watched = m;
  const real = m.kernel.bind(m);
  m.kernel = (id, a, f) => {
    if (id === DRAW_CONTROL) {
      const o = m.resolveTarget(null, a[0]) as { def?: { name?: string }; scriptNo?: number } | null;
      if (o) controls.push({ name: o.def?.name ?? '?', type: m.prop(o, 'type'),
                             text: m.stringAt(m.prop(o, 'text'), o.scriptNo ?? 0),
                             at: m.prop(o, 'text'), from: o.scriptNo ?? 0 });
    }
    return real(id, a, f);
  };
  // What a control puts on the screen is the only proof it was drawn.
  const screen = s.screen as unknown as { text: (...a: unknown[]) => number };
  const realText = screen.text.bind(screen);
  screen.text = (...a: unknown[]) => { drawn.push(String(a[1])); return realText(...a); };
};

let st = s.tick();
const step = (n: number) => { for (let i = 0; i < n; i++) { clock += 1000 / 60; st = s.tick(); watch(); } };
const type = (text: string) => {
  for (const ch of text) { s.key(ch.charCodeAt(0)); step(4); }
};
const press = (k: number, n = 40) => { s.key(k); step(n); };

watch();
step(36000);
check(st.picture === 25, `the game is on the beach (picture ${st.picture})`);

// The save dialog, which used to say the disk was full.
controls = [];
press(F5);
const prompt = controls.find(c => c.type === 2)?.text ?? '';
check(/description of this saved game/.test(prompt),
  `F5 asks for a name: ${JSON.stringify(prompt)}`);
check(controls.some(c => c.type === 6), 'and shows the list of games already saved');
check(!drawn.some(t => /Change|Directory/.test(t)),
  'with no "Change Directory" on the screen, which would lead nowhere');

type('by the sea');
press(ENTER, 60);
check(s.saves.get(0)?.name === 'by the sea',
  `naming it and pressing return saves it: ${JSON.stringify([...s.saves].map(([k, v]) => `${k}:${v.name}`))}`);

// Somewhere else, and a second game of its own.
for (let k = 0; k < 40 && st.picture === 25; k++) { s.key(0x4D00); step(30); }
for (let k = 0; k < 20; k++) { s.key(0x4D00); step(12); }
const away = st.picture;
check(away !== 25, `she walks away to another room (${away})`);

controls = [];
press(F5);
const field = controls.filter(c => c.type === 3).pop()?.text ?? '';
check(field === 'by the sea',
  `the dialog offers the game already saved to write over: ${JSON.stringify(field)}`);
for (let i = 0; i < 40; i++) { s.key(BACKSPACE); step(3); }
type('past the rocks');
press(ENTER, 60);
check(s.saves.get(1)?.name === 'past the rocks' && s.saves.get(0)?.name === 'by the sea',
  `a new name takes a slot of its own: ${JSON.stringify([...s.saves].map(([k, v]) => `${k}:${v.name}`))}`);

/**
 * Small enough for a browser to keep, and the same after a round trip.
 *
 * Both saves were made from inside the dialog, which is one cycle that
 * never ends -- it polls `GetEvent` in a loop, cloning an `Event` each
 * time round, and nothing is collected until a cycle begins.  Saving
 * every clone still in the machine wrote thirteen megabytes, three
 * times what a browser will store, so the page kept nothing: the save
 * worked, restoring worked while the game was up, and it was gone as
 * soon as the game was left.  Only what the game can still reach is
 * part of the save.
 *
 * The catalogue is then put back from its own JSON, so what the restore
 * below works from is exactly what a browser would have handed back.
 */
const text = JSON.stringify([...s.saves]);
check(text.length < 256 * 1024,
  `both saved games together are ${Math.round(text.length / 1024)}KB, small enough to keep`);
s.saves.clear();
for (const [slot, e] of JSON.parse(text)) s.saves.set(slot, e);

// The restore dialog, and the room the save was made in.
controls = [];
drawn = [];
press(F7);
const list = controls.find(c => c.type === 6);
const at = (i: number) => vm().stringAt((list?.at ?? 0) + i * 36, list?.from ?? 0);
check(!!list && at(0) === 'by the sea' && at(1) === 'past the rocks',
  `F7 lists both games: ${JSON.stringify([at(0), at(1)])}`);
check(drawn.includes('by the sea') && drawn.includes('past the rocks'),
  `and both are drawn in the box: ${JSON.stringify(drawn.filter(t => /sea|rocks/.test(t)))}`);

press(DOWN, 20);
press(ENTER, 600);
check(st.picture === away,
  `restoring the second one puts her back in room ${away}, where it was saved (she is in ${st.picture})`);

console.log(`\n${checked - failed}/${checked} saved-game dialog checks passed`);
process.exit(failed ? 1 : 0);
