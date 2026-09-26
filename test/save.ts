/**
 * Saving a game and getting it back.
 *
 * ScummVM's `gamestate_restore` resets the engine, reads the segment
 * manager back -- scripts' locals, clones, the object heap -- puts the
 * stack and clones together again, and then aborts whatever was
 * running and re-enters `play` with `gameIsRestarting` set to restore
 * rather than restart.  Nothing about the screen is kept: the scripts
 * are handed their globals and `Game::replay` builds the room again.
 * That is the shape followed here, on top of the machinery a restart
 * already needed.
 *
 * The two kernels answer opposite ways round, which is ScummVM's doing
 * and worth a check of its own: `kSaveGame` gives back true when it
 * worked, and `kRestoreGame` gives back nothing when it worked, true
 * being the failure.
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

const g = new Game(nodeSource(join(ROOT, 'KQ4')));
const idx = new Index(g);
const s = new Session(g, idx);
let clock = 0;
s.now = () => clock;
const s16 = (v: number) => (v << 16) >> 16;
const step = (n: number) => { for (let i = 0; i < n; i++) { clock += 1000 / 60; st = s.tick(); } };

let st = s.tick();
for (let i = 0; i < 36000 && st.running; i++) { clock += 1000 / 60; st = s.tick(); }

interface Machine {
  objects?: Map<number, unknown>;
  prop(o: unknown, n: string): number;
  kernel(id: number, a: number[], f?: unknown): number;
  makeString(t: string): number;
  restarting: number;
}
const vm = () => s.vm as unknown as Machine;
const ego = () => [...(vm().objects?.values() ?? [])]
  .find((o) => (o as { def?: { name?: string } })?.def?.name === 'ego');
const where = () => `${s16(vm().prop(ego(), 'x'))},${s16(vm().prop(ego(), 'y'))} in ${st.picture}`;

const saveGame = idx.kernel.indexOf('SaveGame');
const restoreGame = idx.kernel.indexOf('RestoreGame');
check(saveGame > 0 && restoreGame > 0, 'the game has both kernels to call');

const home = where();
check(st.picture === 25, `she is on the beach (${home})`);

/**
 * Saved the way a script does it.
 *
 * The number the dialog hands over is not a slot.  Sierra's save dialog
 * counts the games it found and passes that count, and anything below a
 * hundred means "somewhere new"; a hundred and up names one of the
 * games the catalogue listed, counting from a hundred.  Passing the
 * number through as a slot meant every save after the first landed on
 * top of the one before.
 */
const ok = vm().kernel(saveGame, [vm().makeString('kq4'), 0, vm().makeString('by the sea'), 0], null);
check(ok === 1, `saving answers true for success (${ok}), as kSaveGame does`);
check(s.saves.get(0)?.name === 'by the sea',
  `and the first free slot holds it: ${JSON.stringify(s.saves.get(0)?.name ?? '')}`);
vm().kernel(saveGame, [vm().makeString('kq4'), 1, vm().makeString('and again'), 0], null);
check(s.saves.get(1)?.name === 'and again' && s.saves.get(0)?.name === 'by the sea',
  `a second new save takes a slot of its own (${[...s.saves].map(([k, v]) => `${k}:${v.name}`).join(', ')})`);
vm().kernel(saveGame, [vm().makeString('kq4'), 100, vm().makeString('over the top'), 0], null);
check(s.saves.get(0)?.name === 'over the top' && s.saves.size === 2,
  `and a number in the official range replaces that game (${[...s.saves].map(([k, v]) => `${k}:${v.name}`).join(', ')})`);
vm().kernel(saveGame, [vm().makeString('kq4'), 0, vm().makeString('by the sea'), 0], null);

// Somewhere else entirely.
for (let k = 0; k < 40 && st.picture === 25; k++) { s.key(0x4D00); step(30); }
for (let k = 0; k < 20; k++) { s.key(0x4D00); step(12); }
const away = where();
check(st.picture !== 25, `she walks away to another room (${away})`);

// And back.
const failedRestore = vm().kernel(restoreGame, [vm().makeString('kq4'), 109, 0], null);
check(failedRestore === 1, `restoring a slot that is empty answers true for failure (${failedRestore})`);

const good = vm().kernel(restoreGame, [vm().makeString('kq4'), 102, 0], null);
check(good === 0, `restoring answers nothing for success (${good}), as kRestoreGame does`);
step(400);
check(where() === home, `and she is back where she was saved (${where()}, saved at ${home})`);

console.log(`\n${checked - failed}/${checked} save checks passed`);
process.exit(failed ? 1 : 0);
