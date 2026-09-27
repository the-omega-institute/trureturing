#!/usr/bin/env python3
"""Find Erdos problems still labelled OPEN whose own page says they follow from a
problem that has since been settled.

The database records dependencies between problems in prose ("a positive answer
follows from [986]"). If the cited problem is later settled, the citing problem may be
settled with it while its own page still reads open. A sweep that reads one problem at
a time cannot see this, because the evidence sits on a different page.

Input is a directory of cached problem pages named <id>.html, plus the JSON written by
erdos-claim-scan.py so that candidates already claimed or attended can be marked.

Two page facts drive the scan and both are easy to get wrong, so both are asserted
against known pages before any result is printed:

  * the status badge lives in a tooltip inside the prize div and may carry a "(LEAN)"
    suffix, so a bare [A-Z ]+ class silently drops 302 of 1221 real pages;
  * the dependency prose sits in the editorial commentary *after* the content div, so
    reading the content div alone finds the statement and none of the dependencies.

Pages for ids that do not exist answer "No results found" and are skipped, not counted.
"""
import argparse, html, json, os, re, sys

IMPLIES = re.compile(
    r"(follows? from|would follow from|follows? immediately from|is implied by|"
    r"would be implied by|is a special case of|is equivalent to|would follow if|implies)",
    re.I)
SETTLED = {"PROVED", "DISPROVED", "SOLVED"}
BADGE = re.compile(r'<div id="prize">.*?<span class="tooltip">\s*([A-Z()\- ]+?)\s*<span', re.S)


def badge(page):
    m = BADGE.search(page)
    return re.sub(r"\s*\(LEAN\)", "", m.group(1).strip()) if m else None


def body(page):
    """Statement plus the commentary that follows it."""
    i = page.find('<div class="problem-box"')
    j = page.find("Proof expositions")
    return page[i:j] if 0 <= i < j else ""


def plain(fragment):
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", fragment))).strip()


def load(cache):
    pages = {}
    for name in os.listdir(cache):
        if not name.endswith(".html"):
            continue
        page = open(os.path.join(cache, name), encoding="utf-8", errors="replace").read()
        if "No results found" in page:
            continue                      # id does not exist; not a parse failure
        pages[int(name[:-5])] = (badge(page), body(page))
    return pages


def ladder(pages):
    """#920 pins both page facts: it is badged SOLVED (not OPEN) and its dependency on
    #986 appears only in the commentary. A parser that misreads either one reports it
    as an open problem with a stale edge, which is what an unchecked scan claims."""
    if 920 not in pages or 986 not in pages:
        return "ladder needs #920 and #986 in the cache"
    if pages[920][0] != "SOLVED":
        return f"ladder: #920 badge is {pages[920][0]!r}, expected 'SOLVED'"
    if pages[986][0] != "PROVED":
        return f"ladder: #986 badge is {pages[986][0]!r}, expected 'PROVED'"
    if '<a href="/986"' not in pages[920][1]:
        return "ladder: #920 body does not contain its reference to #986"
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cache", default="erdos-cache")
    ap.add_argument("--claims", default="claims.json")
    args = ap.parse_args()

    pages = load(args.cache)
    bad = ladder(pages)
    if bad:
        print(bad, file=sys.stderr)
        return 1
    print(f"ladder: ok (#920 SOLVED, #986 PROVED, edge in commentary)", file=sys.stderr)

    claims = {x["n"]: x for x in json.load(open(args.claims))}
    total, edges = 0, []
    for a, (b, c) in sorted(pages.items()):
        if b != "OPEN":
            continue
        for m in re.finditer(r'<a href="/(\d+)"', c):
            g = int(m.group(1))
            if g == a or g not in pages or pages[g][0] not in SETTLED:
                continue
            total += 1
            window = plain(c[max(0, m.start() - 320):m.start() + 140])
            if IMPLIES.search(window):
                edges.append((a, g, pages[g][0], window[-300:]))

    opens = sum(1 for b, _ in pages.values() if b == "OPEN")
    print(f"real pages: {len(pages)}  OPEN: {opens}")
    print(f"OPEN pages citing a settled problem: {total}")
    print(f"  of those whose prose carries implication language: {len(edges)}\n")
    for a, g, gb, window in edges:
        cl = claims.get(a, {})
        free = cl.get("claims") == 0 and not cl.get("working")
        tag = "FREE" if free else f"claims={cl.get('claims')} working={cl.get('working')}"
        print(f"#{a} -> #{g} [{gb}]  {tag}")
        print(f"    ...{window}\n")
    return 0


sys.exit(main())
