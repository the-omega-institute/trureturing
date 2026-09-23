#!/usr/bin/env python3
"""Collect OEIS entries whose own text states a conjecture, and say which look settled.

Usage: oeis-conjecture-scan.py <search-query> [pages]
   or: oeis-conjecture-scan.py --ids A123456,A234567

Settlement is read from the entry itself: OEIS records a proof, an attribution or a link in a
later comment on the same entry. A missing marker is not proof of openness — it is the absence of
one signal — so the output separates "settled, here is the line" from "no marker found", and never
reports the second as open.
"""
import json, re, sys, time, urllib.parse, urllib.request

UA = {"User-Agent": "trureturing-openproblem/1.0"}
SETTLED = re.compile(
    # "Proof:" opens a settlement comment and carries no article, which is how the
    # settlement of A324605's even-width statement was missed on the first pass.
    r"(?:^|\s)Proof\s*:"
    r"|\b(proved|proven|a proof|the proof|see the proof|is true|are true|now proved"
    r"|was shown|has been shown|follows from|disproved|counterexample found"
    r"|no longer a conjecture|theorem of)\b"
    # A settlement does not have to use the word "proof". A034448's conjecture of 2017-08-20
    # was answered one line below it on 2021-03-19 with "This conjecture is easily verified
    # since all the functions involved are multiplicative and proving it for prime powers is
    # straightforward", and the pattern above read that entry as carrying no marker. A lane was
    # one step from being opened on it. These phrasings are anchored to the word "conjecture"
    # or to an explicit verification verb so that an entry merely calling its own *formula*
    # straightforward is not swept up: a false settled marker discards a live target, which is
    # the more expensive direction of the two.
    r"|\bconjecture\b[^.]{0,80}?\b(is|was|can be|has been)\b[^.]{0,40}?"
    r"\b(easily |readily |straightforwardly |trivially |immediately )?"
    r"(verified|verifiable|checked|settled|established|resolved|answered|confirmed)\b"
    r"|\b(verification|proof) of (this|the) conjecture\b"
    r"|\bthis conjecture (is|was) (easy|straightforward|immediate|trivial)\b"
    # A refutation settles a conjecture as surely as a proof does, and the entry states it in the
    # entry's own voice rather than with the word "disproved". A257750 carries "The conjecture
    # that b < sqrt(n) is false" with three explicit counterexamples, and the pattern above read
    # both its conjecture lines as unmarked.
    r"|\bconjecture\b[^.]{0,80}?\b(is|was|turns out to be)\b[^.]{0,30}?\b(false|incorrect|wrong)\b"
    r"|\brefut(ed|es|ation)\b", re.I)
CONJ = re.compile(r"\bconjectur", re.I)

def fetch(url, tries=3):
    last = None
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers=UA)
            with urllib.request.urlopen(req, timeout=45) as r:
                return r.read().decode("utf-8", "replace")
        except Exception as exc:
            last = exc
            time.sleep(2 * (i + 1))
    raise SystemExit(f"FETCH_FAILED {url}: {last}")

def search(query, start):
    u = ("https://oeis.org/search?fmt=text&start=%d&q=%s"
         % (start, urllib.parse.quote(query)))
    return fetch(u)

def anums(text):
    return re.findall(r"^%I (A\d{6})", text, re.M)

def entry(a):
    return fetch("https://oeis.org/search?fmt=text&q=" + urllib.parse.quote("id:" + a))

def lines(text, tag):
    return [l for l in text.splitlines() if l.startswith("%" + tag + " ")]

def main():
    if len(sys.argv) < 2:
        raise SystemExit("usage: oeis-conjecture-scan.py <query> [pages] | --ids A1,A2")
    out = []
    if sys.argv[1] == "--ids":
        seen = [x.strip() for x in sys.argv[2].split(",") if x.strip()]
    else:
        query = sys.argv[1]
        pages = int(sys.argv[2]) if len(sys.argv) > 2 else 3
        seen = []
        for p in range(pages):
            t = search(query, p * 10)
            got = anums(t)
            if not got:
                break
            seen.extend(got)
        seen = list(dict.fromkeys(seen))
    for a in seen:
        txt = entry(a)
        body = lines(txt, "C") + lines(txt, "F")
        # A settlement comment usually names the thing it settles, so it contains the word
        # "conjecture" too. Treating such a line as a NEW conjecture terminates the search window
        # of the conjecture it settles, and the real conjecture is then reported as unmarked —
        # which is exactly how A034448 read as open five years after it was answered one line
        # below. A line that carries a settlement marker is a marker, not a fresh statement,
        # unless it introduces one with an explicit "Conjecture:".
        def starts_conjecture(line):
            if not CONJ.search(line):
                return False
            if SETTLED.search(line) and not re.search(r"\bconjecture\s*:", line, re.I):
                return False
            return True

        conj_idx = [i for i, l in enumerate(body) if starts_conjecture(l)]
        if not conj_idx:
            continue
        # Settlement is per conjecture, not per entry. An entry can carry five conjectures and one
        # proof; reporting the entry as settled would discard four live targets. A settlement
        # comment follows the statement it settles, so each conjecture takes the markers between
        # it and the next conjecture line.
        items = []
        for j, i in enumerate(conj_idx):
            stop = conj_idx[j + 1] if j + 1 < len(conj_idx) else len(body)
            near = [l for l in body[i + 1:stop] if SETTLED.search(l)]
            own = [body[i]] if SETTLED.search(body[i]) else []
            marks = own + near
            items.append({"conjecture": body[i], "settlement_lines": marks,
                          "status": "settled-marker" if marks else "no-marker"})
        out.append({"a": a, "conjectures": items,
                    "status": "settled-marker" if all(x["status"] == "settled-marker"
                                                      for x in items) else "mixed-or-open"})
        time.sleep(0.4)
    json.dump(out, sys.stdout, ensure_ascii=False, indent=1)
    print()

if __name__ == "__main__":
    main()
