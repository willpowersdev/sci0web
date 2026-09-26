/**
 * How a picture arrives.
 *
 * SCI0 asks for a transition by number in `DrawPic`, and the numbers
 * are not the ones later versions use: the interpreter carried a table
 * translating them, which ScummVM keeps as `oldTransitionIDs`.  Four
 * entries here were guessed at rather than read, and guessed wrong.
 * 6 and 7 are the diagonal rolls -- all four edges moving at once,
 * which is a square shrinking onto the middle of the screen or growing
 * out of it -- and they were being drawn as the vertical rolls, a pair
 * of columns.  King's Quest IV opens with two pictures that ask for 6,
 * so the very first thing the game does was the wrong shape.  40 to 43
 * are scrolls, where the old picture is pushed off the edge while the
 * new one follows it on, and they were being drawn as plain wipes that
 * painted over it.
 *
 * The blackout flag was wrong too, in the other direction: bit 15 of
 * the flags does nothing before SCI1 late, because the translation
 * table says for each old number whether it blacks out and ScummVM's
 * `doit` overwrites the flag with it.  Blacking out is two passes --
 * the paired transition painting the old picture black, then the asked
 * for one bringing the new one in -- and it was one pass with the
 * unreached part drawn black, which is not the same thing at all.
 */
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { Game, type ResourceSource } from '../src/resources.ts';
import { Index } from '../src/script.ts';
import { Session } from '../src/vm/session.ts';
import { Screen, WIDTH, HEIGHT, wipeFor, type Wipe } from '../src/vm/screen.ts';
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

/**
 * The insides a transition works on, which is what its shape is.
 *
 * Not an intersection with `Screen`: the two fields are private there,
 * and TypeScript reduces an intersection that redeclares a private
 * member to `never`.
 */
interface Inner { wipeMask: Uint8Array; wipeFrom: Uint8Array; visual: Uint8Array }
const inner = (s: Screen) => s as unknown as Inner;

/** ScummVM's `oldTransitionIDs`, as a table to be matched, not derived. */
const SCUMMVM: Array<[number, Wipe, boolean]> = [
  [0, 'vroll-from-centre', false], [1, 'hroll-from-centre', false],
  [2, 'straight-from-right', false], [3, 'straight-from-left', false],
  [4, 'straight-from-bottom', false], [5, 'straight-from-top', false],
  [6, 'droll-to-centre', false], [7, 'droll-from-centre', false],
  [8, 'blocks', false],
  [9, 'vroll-to-centre', false], [10, 'hroll-to-centre', false],
  [11, 'straight-from-right', true], [12, 'straight-from-left', true],
  [13, 'straight-from-bottom', true], [14, 'straight-from-top', true],
  [15, 'droll-to-centre', true], [16, 'droll-from-centre', true],
  [17, 'blocks', true],
  [18, 'pixels', false], [27, 'pixels', true],
  [30, 'fade', false],
  [40, 'scroll-right', false], [41, 'scroll-left', false],
  [42, 'scroll-up', false], [43, 'scroll-down', false],
  [100, 'none', false],
];
const wrong = SCUMMVM.filter(([id, style, blackout]) => {
  const [got, black] = wipeFor(id);
  return got !== style || black !== blackout;
});
check(wrong.length === 0,
  `all ${SCUMMVM.length} old transition numbers translate as ScummVM translates them` +
  (wrong.length ? `: ${wrong.map(([id, s]) => `${id} wanted ${s}, got ${wipeFor(id)[0]}`).join('; ')}` : ''));

/** The box round everything a transition has not reached yet. */
function unreached(s: Inner) {
  let x0 = WIDTH, y0 = HEIGHT, x1 = -1, y1 = -1, n = 0;
  for (let y = 0; y < HEIGHT; y++)
    for (let x = 0; x < WIDTH; x++)
      if (!s.wipeMask[y * WIDTH + x]) {
        n++;
        if (x < x0) x0 = x; if (x > x1) x1 = x;
        if (y < y0) y0 = y; if (y > y1) y1 = y;
      }
  return { x0, y0, x1, y1, n };
}

// Six is a square closing in: the thing King's Quest IV opens with.
{
  const s = new Screen();
  s.beginWipe(wipeFor(6)[0], false, 0);
  const boxes = [0, 100, 200, 300].map(t => { s.advanceWipe(t); return unreached(inner(s)); });
  const shrinking = boxes.every((b, i) =>
    i === 0 || (b.x0 > boxes[i - 1].x0 && b.y0 > boxes[i - 1].y0 &&
                b.x1 < boxes[i - 1].x1 && b.y1 < boxes[i - 1].y1));
  check(shrinking, `what it has not reached is a rectangle closing on all four sides: ` +
    boxes.map(b => `${b.x1 - b.x0}x${b.y1 - b.y0}`).join(' -> '));
  const last = boxes[boxes.length - 1];
  check(Math.abs((last.x0 + last.x1) / 2 - WIDTH / 2) < 4 &&
        Math.abs((last.y0 + last.y1) / 2 - HEIGHT / 2) < 4,
    `and it closes on the middle (${(last.x0 + last.x1) / 2}, ${(last.y0 + last.y1) / 2})`);
  s.advanceWipe(400);
  check(!s.wiping, 'and it is over in the 380 milliseconds SCI spends on it');
}

// And seven is the same square the other way about.
{
  const s = new Screen();
  s.beginWipe(wipeFor(7)[0], false, 0);
  const sizes = [40, 120, 200].map(t => {
    s.advanceWipe(t);
    const m = inner(s).wipeMask;
    let x0 = WIDTH, x1 = -1, y0 = HEIGHT, y1 = -1;
    for (let y = 0; y < HEIGHT; y++)
      for (let x = 0; x < WIDTH; x++)
        if (m[y * WIDTH + x]) {
          if (x < x0) x0 = x; if (x > x1) x1 = x;
          if (y < y0) y0 = y; if (y > y1) y1 = y;
        }
    return { w: x1 - x0, h: y1 - y0 };
  });
  check(sizes.every((b, i) => i === 0 || (b.w > sizes[i - 1].w && b.h > sizes[i - 1].h)),
    `seven grows the square instead: ${sizes.map(b => `${b.w}x${b.h}`).join(' -> ')}`);
}

// Every one of them finishes, and leaves the new picture showing.
{
  const ALL: Wipe[] = ['pixels', 'blocks', 'fade',
    'straight-from-left', 'straight-from-right', 'straight-from-top', 'straight-from-bottom',
    'vroll-from-centre', 'vroll-to-centre', 'hroll-from-centre', 'hroll-to-centre',
    'droll-from-centre', 'droll-to-centre'];
  const bad: string[] = [];
  for (const style of ALL) {
    const s = new Screen();
    s.beginWipe(style, false, 0);
    let t = 0;
    while (s.wiping && t < 20000) { t += 10; s.advanceWipe(t); }
    // The shift registers never visit their starting cell, which SCI
    // lives with too; anything else must cover the screen outright.
    const left = [...inner(s).wipeMask].filter(v => !v).length;
    const slack = style === 'pixels' ? 1 : style === 'blocks' ? 64 : 0;
    if (s.wiping || left > slack) bad.push(`${style} (${s.wiping ? 'never ended' : `${left} left`})`);
  }
  check(bad.length === 0, `all ${ALL.length} painting transitions cover the screen and end${bad.length ? `: ${bad.join(', ')}` : ''}`);
}

// Blacking out is two passes, not one drawn dark.
{
  const s = new Screen();
  inner(s).visual.fill(0x22);
  s.beginWipe('droll-from-centre', true, 0);
  const black = () => [...inner(s).wipeFrom].filter(v => v === 0).length;
  const reached = () => [...inner(s).wipeMask].filter(v => v).length;
  s.advanceWipe(200);
  check(black() > 20000 && reached() === 0,
    `the first pass paints the old picture black and shows none of the new one (${black()} black, ${reached()} arrived)`);
  s.advanceWipe(600);
  check(black() === WIDTH * HEIGHT && reached() > 20000,
    `the second brings the new one in over it (${reached()} arrived)`);
  s.advanceWipe(800);
  check(!s.wiping, 'and both passes are done');
}

// A scroll moves the old picture rather than painting over it.
{
  const s = new Screen();
  const px = inner(s);
  for (let i = 0; i < WIDTH * HEIGHT; i++) px.visual[i] = 0x11;
  s.beginWipe('scroll-left', false, 0);
  for (let i = 0; i < WIDTH * HEIGHT; i++) px.visual[i] = 0x99;
  s.advanceWipe(400);
  const out = s.rgb();
  const top = s.statusVisible ? 10 : 0;
  const at = (x: number) => out[((top + HEIGHT / 2) * WIDTH + x) * 3 + 2];
  const old = at(4), fresh = at(WIDTH - 4);
  check(old !== fresh,
    `half way through, the left of the screen is still the old picture and the right is the new one (${old} vs ${fresh})`);
  check([...px.wipeMask].every(v => !v),
    'and it paints over nothing: a scroll is the two pictures at an offset');
}

// What King's Quest IV actually asks for, from the game itself.
{
  const g = new Game(nodeSource(join(ROOT, 'KQ4')));
  const idx = new Index(g);
  const s = new Session(g, idx);
  let clock = 0;
  s.now = () => clock;
  const asked: number[] = [];
  const DRAWPIC = idx.kernel.indexOf('DrawPic');
  let watched: unknown = null;
  const watch = () => {
    const m = s.vm as unknown as { kernel(i: number, a: number[], f?: unknown): number };
    if (m === watched) return;
    watched = m;
    const real = m.kernel.bind(m);
    m.kernel = (id, a, f) => {
      if (id === DRAWPIC) asked.push((a[1] ?? 0) & 0xFF);
      return real(id, a, f);
    };
  };
  watch();
  let st = s.tick();
  for (let i = 0; i < 4000 && st.running && asked.length < 2; i++) { clock += 1000 / 60; st = s.tick(); watch(); }
  check(asked.length >= 2 && asked[0] === 6 && asked[1] === 6,
    `the game's first two pictures ask for transition 6 (${asked.slice(0, 2).join(', ')})`);
  check(wipeFor(asked[0] ?? -1)[0] === 'droll-to-centre',
    `which is the square shrinking onto the middle (${wipeFor(asked[0] ?? -1)[0]})`);
}

console.log(`\n${checked - failed}/${checked} transition checks passed`);
process.exit(failed ? 1 : 0);
