import { createServer } from 'node:http';
import { readFile, readdir, stat } from 'node:fs/promises';
import { extname, join, normalize } from 'node:path';
const TYPES = { '.html':'text/html', '.js':'text/javascript', '.json':'application/json', '.css':'text/css', '.png':'image/png' };
const root = process.cwd();
/**
 * Games are served read-only from their own directory so the page can be
 * opened straight at one (`/?game=qfg2`) instead of going through the
 * directory picker, which needs a click and a native dialog.
 *
 * `games/` beside the page by default, which is where a deployed copy
 * keeps them: the same folder, at the same place, so what is developed
 * against is what is uploaded.  It used to default to the whole Sierra
 * collection somewhere else entirely, which meant the list here and the
 * list on the web were different lists -- fifteen against eight, under
 * different names, and half of them games this interpreter cannot read.
 *
 * `SCI_GAMES` still points it anywhere else, which is what the tests
 * use to reach an untrimmed copy.
 */
const GAMES = process.env.SCI_GAMES ?? join(root, 'games');
createServer(async (req, res) => {
  const url = (req.url ?? '/').split('?')[0];
  let path, base;
  if (url === '/games' || url.startsWith('/games/')) {
    base = GAMES;
    path = join(GAMES, normalize(url.slice('/games'.length) || '/'));
  } else {
    base = root;
    path = join(root, normalize(url === '/' ? '/index.html' : url));
  }
  if (!path.startsWith(base)) { res.writeHead(403).end(); return; }
  // A directory listing lets the page discover which games are present.
  if (base === GAMES) {
    try {
      const st = await stat(path);
      if (st.isDirectory()) {
        const names = await readdir(path);
        // The top-level listing answers "which of these are games", which
        // is a question only the server can answer cheaply: a directory
        // holding a RESOURCE.MAP is one, and anything else on the way --
        // .DS_Store, stray folders -- is not worth offering.
        // join() leaves the trailing slash of "/games/" on the path, so
        // compare without it rather than against the bare directory.
        if (path.replace(/\/+$/, '') === GAMES) {
          const games = [];
          for (const n of names.sort()) {
            if (n.startsWith('.')) continue;
            try {
              const inner = await readdir(join(GAMES, n));
              if (inner.some(f => /^RESOURCE\.MAP$/i.test(f))) games.push(n);
            } catch { /* not a directory */ }
          }
          res.writeHead(200, { 'content-type': 'application/json' });
          res.end(JSON.stringify(games));
          return;
        }
        res.writeHead(200, { 'content-type': 'application/json' });
        res.end(JSON.stringify(names));
        return;
      }
    } catch { res.writeHead(404).end('not found'); return; }
  }
  try {
    const body = await readFile(path);
    res.writeHead(200, {
      'content-type': TYPES[extname(path)] ?? 'application/octet-stream',
      // With no cache headers at all a browser falls back to heuristic
      // caching and will happily serve a stale bundle after a rebuild,
      // which looks exactly like a feature that was never added.  The
      // game files are large and never change, so only the app's own
      // files are marked uncacheable.
      ...(base === GAMES
        ? { 'cache-control': 'public, max-age=3600' }
        : { 'cache-control': 'no-store, must-revalidate' }),
    });
    res.end(body);
  } catch { res.writeHead(404).end('not found'); }
// `PORT=0` asks the system for a free one, which is how the page test
// runs a server of its own without colliding with a copy already up.
}).listen(Number(process.env.PORT ?? 8017), function () {
  console.log(`serving http://localhost:${this.address().port}`);
});
