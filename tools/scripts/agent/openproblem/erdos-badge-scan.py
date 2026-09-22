#!/usr/bin/env python3
"""Fetch erdosproblems.com problem pages and report the status badge of each.

The site publishes its own decidability vocabulary: VERIFIABLE (open, a finite example would
prove it), FALSIFIABLE (open, a finite counterexample would disprove it) and DECIDABLE
(resolved up to a finite check) are exactly CLAUDE.md tier 2; plain OPEN pages say in so many
words that the problem "cannot be resolved with a finite computation" (tier 3). Filtering by
badge is therefore the selection function; filtering by statement shape is not, and a blind
shape sweep of 1217 statements returned zero usable candidates.

Pages are cached under --cache so a re-run costs no requests. Exit 0 always; unreachable pages
are reported as UNREACHABLE rather than silently dropped, because an unmeasured page must not
look like an absent badge.
"""
import argparse, concurrent.futures as cf, json, os, re, sys, urllib.error, urllib.request

BADGES = ("VERIFIABLE", "FALSIFIABLE", "DECIDABLE", "OPEN", "PROVED", "DISPROVED", "SOLVED")
UA = "trureturing-openproblem-scan/1 (+https://github.com/the-omega-institute/trureturing)"

def fetch(n, cache, timeout):
    path = os.path.join(cache, f"{n}.html")
    if os.path.exists(path) and os.path.getsize(path) > 2000:
        return open(path, encoding="utf-8", errors="replace").read()
    req = urllib.request.Request(f"https://www.erdosproblems.com/{n}", headers={"User-Agent": UA})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            if r.status != 200:
                return None
            body = r.read().decode("utf-8", "replace")
    except (urllib.error.URLError, TimeoutError, OSError):
        return None
    open(path, "w", encoding="utf-8").write(body)
    return body

def parse(n, html):
    if html is None:
        return {"n": n, "badge": "UNREACHABLE", "prize": None, "lean": None, "statement": None}
    m = re.search(r'<div id="prize">(.*?)</div>', html, re.S)
    block = m.group(1) if m else ""
    badge = next((b for b in BADGES if re.search(rf"\b{b}\b", block)), None)
    if badge is None:
        badge = next((b for b in BADGES if re.search(rf"\b{b}\b", html)), "NO-BADGE")
    prize = (re.search(r"\$\s*([0-9,]+)", block) or [None, None])[1]
    lean = bool(re.search(r"\(LEAN\)|verified in Lean", html))
    c = re.search(r'<div id="content">(.*?)</div>', html, re.S)
    st = re.sub(r"<[^>]+>", " ", c.group(1)) if c else ""
    st = re.sub(r"\s+", " ", st).strip()
    return {"n": n, "badge": badge, "prize": prize, "lean": lean, "statement": st}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", type=int, default=1)
    ap.add_argument("--end", type=int, default=1200)
    ap.add_argument("--cache", required=True)
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--timeout", type=int, default=25)
    ap.add_argument("--badges", default="", help="comma list; empty = all")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()
    os.makedirs(a.cache, exist_ok=True)
    want = {b.strip().upper() for b in a.badges.split(",") if b.strip()}
    rows = []
    with cf.ThreadPoolExecutor(max_workers=a.workers) as ex:
        futs = {ex.submit(fetch, n, a.cache, a.timeout): n for n in range(a.start, a.end + 1)}
        for f in cf.as_completed(futs):
            rows.append(parse(futs[f], f.result()))
    rows.sort(key=lambda r: r["n"])
    sel = [r for r in rows if not want or r["badge"] in want]
    if a.json:
        json.dump(sel, sys.stdout, ensure_ascii=False, indent=1)
        print()
    else:
        tally = {}
        for r in rows:
            tally[r["badge"]] = tally.get(r["badge"], 0) + 1
        for b, c in sorted(tally.items(), key=lambda kv: -kv[1]):
            print(f"{b:<12} {c}", file=sys.stderr)
        for r in sel:
            print(f"#{r['n']:<5} {r['badge']:<12} lean={'Y' if r['lean'] else 'n'} "
                  f"prize={r['prize'] or '-':<6} {r['statement'][:150]}")
    return 0

sys.exit(main())
