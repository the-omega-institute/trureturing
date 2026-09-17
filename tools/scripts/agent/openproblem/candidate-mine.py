#!/usr/bin/env python3
"""Mine OEIS for candidate open problems and drop the ones this repository has already handled.

WHY THIS EXISTS. Candidate supply for the open-problem lane came from a browser-oracle research
seat. That carrier is unreliable: in one session it returned a clarifying question instead of a
list, then failed four consecutive dispatches with `infrastructure_retry_exhausted`,
`extraction_failure` and `prompt_delivery_uncertain`, while review asks on the same carrier
succeeded in the same window. A supply line that stops when one carrier degrades is not a
continuous search, so this is the same search run locally, from the repository's own tools.

It does not replace the oracle seat and does not judge mathematics. It answers one question:
**which OEIS entries state a conjecture that carries no settlement marker and that this repository
has not already touched.** Everything after that — reading the whole entry, downloading every
`%H` paper, the numeric check, the preregistration — is unchanged and still done by hand, because
those are the steps where the expensive mistakes live.

Settlement reading is delegated to `oeis-conjecture-scan.py`, which is the single place that knows
how OEIS records a settlement; duplicating that regex here would be a second source of truth.

**It reads what has landed.** `repo_known` scans the working tree, so an A-number that is only on
an open lane branch or named in a preregistration issue still looks free. Pass those in with
`--exclude` when a lane is in flight; the alternative, querying GitHub from here, would make a
local mining tool fail whenever the network does.

usage: candidate-mine.py [--pages N] [--json] [--exclude A123456,A234567] QUERY [QUERY ...]
       candidate-mine.py --selftest

exit 0 = ran (candidates may be zero), 2 = bad usage, 3 = a scan subprocess failed.
"""
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SCAN = os.path.join(HERE, "oeis-conjecture-scan.py")
REPO = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
A_NUMBER = re.compile(r"\bA\d{6}\b")


def repo_known():
    """Every A-number this repository has already settled, screened out, or written about.

    Read from the working tree rather than a pinned revision: the caller wants to know what is
    taken *now*, and a stale answer here costs a wasted preregistration.
    """
    known = set()
    for rel in ("Problems", "tools/scripts/agent/openproblem/SCREENED-OUT.md", "D5", "Library"):
        path = os.path.join(REPO, rel)
        if not os.path.exists(path):
            continue
        try:
            out = subprocess.run(
                ["git", "grep", "-h", "-o", "-E", r"A[0-9]{6}", "--", rel],
                cwd=REPO, capture_output=True, text=True, timeout=120)
        except (OSError, subprocess.SubprocessError):
            continue
        known.update(A_NUMBER.findall(out.stdout))
    return known


def scan(query, pages):
    r = subprocess.run([sys.executable, SCAN, query, str(pages)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write("scan failed for %r: %s\n" % (query, r.stderr.strip()[:400]))
        return None
    try:
        return json.loads(r.stdout)
    except ValueError:
        sys.stderr.write("scan produced no JSON for %r\n" % query)
        return None


def unmarked(entries):
    """Entries carrying at least one conjecture line with no settlement marker.

    A missing marker is not proof of openness — that is the scanner's own caveat and it holds
    here too. It is a filter for what is worth reading, never a claim that the problem is open.
    """
    out = []
    for e in entries or []:
        live = [c for c in e.get("conjectures", []) if c.get("status") == "no-marker"]
        if live:
            out.append({"a": e["a"], "conjectures": [c["conjecture"] for c in live]})
    return out


def main(argv):
    pages, as_json, queries, excluded = 2, False, [], set()
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--pages":
            i += 1
            if i >= len(argv) or not argv[i].isdigit():
                sys.stderr.write("--pages needs a number\n")
                return 2
            pages = int(argv[i])
        elif a == "--json":
            as_json = True
        elif a == "--exclude":
            i += 1
            if i >= len(argv):
                sys.stderr.write("--exclude needs a comma-separated list of A-numbers\n")
                return 2
            excluded.update(A_NUMBER.findall(argv[i].upper()))
        elif a.startswith("-"):
            sys.stderr.write("unknown option %r\n" % a)
            return 2
        else:
            queries.append(a)
        i += 1
    if not queries:
        sys.stderr.write(__doc__)
        return 2

    known = repo_known() | excluded
    seen, rows, failed = set(), [], 0
    for q in queries:
        entries = scan(q, pages)
        if entries is None:
            failed += 1
            continue
        for cand in unmarked(entries):
            if cand["a"] in known or cand["a"] in seen:
                continue
            seen.add(cand["a"])
            rows.append({"a": cand["a"], "query": q, "conjectures": cand["conjectures"]})

    if as_json:
        json.dump(rows, sys.stdout, ensure_ascii=False, indent=1)
        print()
    else:
        print("queries=%d  candidates=%d  already-known A-numbers in repo=%d"
              % (len(queries), len(rows), len(known)))
        for r in rows:
            print("\n%s  [%s]" % (r["a"], r["query"]))
            for c in r["conjectures"]:
                print("   " + c[:300])
    return 3 if failed and not rows else 0


def selftest():
    fail = 0
    if unmarked([{"a": "A1", "conjectures": [{"conjecture": "x", "status": "settled-marker"}]}]):
        print("[FAIL] settled entries must be dropped")
        fail = 1
    got = unmarked([{"a": "A2", "conjectures": [
        {"conjecture": "keep me", "status": "no-marker"},
        {"conjecture": "drop me", "status": "settled-marker"}]}])
    if got != [{"a": "A2", "conjectures": ["keep me"]}]:
        print("[FAIL] per-conjecture filtering is wrong: %r" % (got,))
        fail = 1
    if main([]) != 2:
        print("[FAIL] no query must exit 2")
        fail = 1
    if main(["--pages", "x", "q"]) != 2:
        print("[FAIL] bad --pages must exit 2")
        fail = 1
    if main(["--exclude"]) != 2:
        print("[FAIL] --exclude without a value must exit 2")
        fail = 1
    k = repo_known()
    if not isinstance(k, set):
        print("[FAIL] repo_known must return a set")
        fail = 1
    if not fail:
        print("CANDIDATE_MINE_SELFTEST=ok  repo_known=%d" % len(k))
    return fail


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "--selftest":
        sys.exit(selftest())
    sys.exit(main(sys.argv[1:]))
