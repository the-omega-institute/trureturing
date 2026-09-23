#!/usr/bin/env python3
"""Record, for each Erdős problem, whether anyone has claimed it or is working on it.

The problem page's badge is not the claim state: #196 carried a full proof claim dated
2026-09-14 while its page still read OPEN. The claim state lives on a separate forum page,
which is the only authority this scan reads.

Two signals are extracted per problem:

  claims   the count from "There is/are N proof claim(s)", or 0 when the page says
           "No proof claims have been submitted yet."
  working  the names listed under "Currently working on", or empty.

A problem worth dispatching a seat at is open, has zero claims and nobody working. Anything
else is somebody else's lane. Pages are cached under --cache so a re-run costs no requests;
unreachable pages are reported as UNKNOWN rather than as zero, because an unmeasured page
must not look like an unclaimed one.
"""
import argparse, concurrent.futures as cf, json, os, re, sys, urllib.error, urllib.request

UA = "trureturing-openproblem-scan/1 (+https://github.com/the-omega-institute/trureturing)"
CLAIMS = "https://www.erdosproblems.com/forum/thread/{n}/proof-claims"
NONE_LINE = "No proof claims have been submitted yet."


def fetch(url, path, timeout):
    if os.path.exists(path) and os.path.getsize(path) > 500:
        return open(path, encoding="utf-8", errors="replace").read()
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            if r.status != 200:
                return None
            body = r.read().decode("utf-8", "replace")
    except (urllib.error.URLError, TimeoutError, OSError):
        return None
    open(path, "w", encoding="utf-8").write(body)
    return body


def text_of(html):
    t = re.sub(r"<script.*?</script>", "", html, flags=re.S)
    t = re.sub(r"<style.*?</style>", "", t, flags=re.S)
    return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", t)).strip()


def scan(n, cache, timeout):
    html = fetch(CLAIMS.format(n=n), os.path.join(cache, f"claims-{n}.html"), timeout)
    if html is None:
        return {"n": n, "claims": None, "working": None}
    t = text_of(html)
    m = re.search(r"There (?:are|is) (\d+) proof claim", t)
    claims = int(m.group(1)) if m else (0 if NONE_LINE in t else None)
    w = re.search(r"Currently working on (.*?) Looks difficult", t)
    working = [] if not w or w.group(1).strip() == "None" else [
        s.strip() for s in w.group(1).split(",") if s.strip()]
    return {"n": n, "claims": claims, "working": working}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", type=int, default=1)
    ap.add_argument("--end", type=int, default=1221)
    ap.add_argument("--cache", required=True)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=25)
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()
    os.makedirs(a.cache, exist_ok=True)
    rows = []
    with cf.ThreadPoolExecutor(max_workers=a.workers) as ex:
        futs = {ex.submit(scan, n, a.cache, a.timeout): n
                for n in range(a.start, a.end + 1)}
        for f in cf.as_completed(futs):
            rows.append(f.result())
    rows.sort(key=lambda r: r["n"])
    if a.json:
        json.dump(rows, sys.stdout, ensure_ascii=False, indent=1)
        print()
        return 0
    unknown = [r for r in rows if r["claims"] is None]
    claimed = [r for r in rows if r["claims"]]
    busy = [r for r in rows if r["claims"] == 0 and r["working"]]
    free = [r for r in rows if r["claims"] == 0 and not r["working"]]
    print(f"scanned={len(rows)} unmeasured={len(unknown)} claimed={len(claimed)} "
          f"zero-claim-but-worked-on={len(busy)} zero-claim-unattended={len(free)}",
          file=sys.stderr)
    for r in claimed:
        print(f"#{r['n']:<5} claims={r['claims']}")
    return 0


sys.exit(main())
