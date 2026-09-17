#!/usr/bin/env python3
"""External OEIS prior-art probe: has anyone outside this repository already
formalised this A-number?

Companion to prior-art.sh, which answers the other half of Rule 11 ("does this
repository already have it"). The design problem here is that a miss must not
read as novelty, so every corpus is queried by a method whose blind spots are
known, every blind spot is printed, and NO OUTPUT OF THIS PROBE EVER ASSERTS
THAT A SEQUENCE HAS NOT BEEN FORMALISED. The strongest thing it says is that the
indexed paths it can see contain no match.

Why Python and not shell: three review rounds on a bash implementation produced
eleven blocking findings, every one of them the same shape — a command whose
failure was not checked, so the failure became a quiet "absent" and exit 0.
Examples that actually reproduced: `die` inside a function called in `$(...)`
exited only the subshell; `grep ... || true` merged read errors with no-match;
a failed `sed` became the number zero; a failed `tr` made two corpora share one
cache file; a jq pipeline's status was discarded while its text was trusted.
In shell that class of defect is the default and must be excluded one call at a
time. Here a failed subprocess raises, a missing key raises, and the only way to
exit 0 is to reach the end of a successful run.

Corpora and the shape each has (measured 2026-09-13, trees untruncated):

  provables/sequencelib   Lean 4 definitions of OEIS sequences, 26,336 paths.
      25,465 distinct A-numbers appear in path names: 25,457 under
      Sequencelib/Synthetic/<prefix>/, 49 under Sequencelib/AISynth/, 1 at top
      level. Those per-directory counts sum to 25,507 rather than 25,465
      because 42 A-numbers appear in more than one directory. Synthetic and
      AISynth files are machine-written DEFINITIONS, not proofs. Observed range
      A000004..A351831, nothing at or above A390000. Blind spot: 29 further
      modules are named by concept (Fibonacci.lean, Catalan.lean, ...) and carry
      their A-numbers only in file contents, which a path query cannot see.

  google-deepmind/formal-conjectures   1,733 paths, of which 227 are
      FormalConjectures/OEIS/<decimal>.lean, the decimal being the A-number with
      the 'A' and leading zeros stripped (A000040 -> 40.lean, verified by
      reading that file). These are open `sorry` statements: a hit means the
      conjecture is written down, not that it is settled.

  plby/lean-proofs   46,436 paths organised by arXiv identifier. ZERO A-numbers
      occur in any path, so this corpus is always reported UNKNOWN. Answering it
      needs a content search of a clone, which this probe does not do.

Usage:
    tools/scripts/agent/oeis-prior-art.py A397349 [A000045 ...]

Exit codes:
    0  no matching indexed path in any corpus that can answer
    3  at least one hit; READ IT before dispatching
    2  bad usage, missing dependency, or any query/validation failure
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

ANUM = re.compile(r"\A[0-9]{6}\Z")
ANUM_IN_PATH = re.compile(r"A[0-9]{6}")
CONCEPT_MODULE = re.compile(r"\ASequencelib/[A-Z][A-Za-z]+\.lean\Z")
FC_OEIS = re.compile(r"\AFormalConjectures/OEIS/([0-9]+)\.lean\Z")

# Measured 2026-09-13. A corpus that has moved materially away from these is not
# one this probe knows how to read, and it says so rather than reporting a miss.
SEQUENCELIB_PATHS = 26336
SEQUENCELIB_ANUMS = 25465
FORMALCONJ_PATHS = 1733
FORMALCONJ_OEIS = 227

SEQUENCELIB = os.environ.get("OEIS_SEQUENCELIB_REPO", "provables/sequencelib")
FORMALCONJ = os.environ.get("OEIS_FORMALCONJ_REPO", "google-deepmind/formal-conjectures")
LEANPROOFS = os.environ.get("OEIS_LEANPROOFS_REPO", "plby/lean-proofs")

class Failure(Exception):
    """Any condition under which a miss could not be trusted."""


def run(argv: list[str]) -> str:
    """Run a command, raising unless it exits 0. No silent failures."""
    try:
        proc = subprocess.run(argv, capture_output=True, text=True)
    except OSError as exc:
        raise Failure(f"could not execute {argv[0]}: {exc}") from exc
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or "").strip().splitlines()
        tail = detail[-1] if detail else "no diagnostic"
        raise Failure(f"{' '.join(argv[:3])} exited {proc.returncode}: {tail}")
    return proc.stdout


def fetch_tree(repo: str, expected: int) -> list[str]:
    """Return every path in a repository's default-branch tree.

    There is deliberately no cache. A cache is a pure optimisation here — this
    probe runs once before a seat is dispatched, not in a loop — and it brought
    an entire trust surface with it: provenance markers, freshness, atomic
    publication, temporary files, key collisions, partial writes. Every one of
    those is a way for a stale or partial tree to become a confident miss, which
    is the single failure this probe exists to prevent. Fetching each time costs
    a few seconds and removes the surface.

    Fails closed on a truncated tree and on a tree materially smaller than the
    corpus is known to be.
    """
    branch = run(["gh", "repo", "view", repo, "--json", "defaultBranchRef",
                  "-q", ".defaultBranchRef.name"]).strip()
    if not branch:
        raise Failure(f"{repo} reported an empty default branch")

    raw = run(["gh", "api", f"repos/{repo}/git/trees/{branch}?recursive=1"])
    try:
        tree = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise Failure(f"{repo} tree response is not JSON: {exc}") from exc

    if tree.get("truncated") is not False:
        raise Failure(f"{repo} tree is truncated or its truncation flag is absent; "
                      "a miss would be a false negative")
    if "tree" not in tree:
        raise Failure(f"{repo} tree response has no 'tree' key")

    try:
        paths = [entry["path"] for entry in tree["tree"]]
    except (KeyError, TypeError) as exc:
        raise Failure(f"{repo} tree contains an entry without a path: {exc}") from exc

    if len(paths) < expected * 0.8:
        raise Failure(f"{repo} returned {len(paths)} paths against roughly {expected} "
                      "expected; the corpus changed shape and a miss would mean nothing")
    return paths


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        raise Failure("usage: oeis-prior-art.py <A-number> [<A-number> ...]")

    # Every argument is validated before any network call is made.
    anums: list[str] = []
    for raw in argv[1:]:
        text = raw.strip().upper()
        if not text.startswith("A") or not ANUM.match(text[1:]):
            raise Failure(f"not an A-number: {raw!r} (expected A followed by exactly six digits)")
        anums.append(text)

    sl_paths = fetch_tree(SEQUENCELIB, SEQUENCELIB_PATHS)
    fc_paths = fetch_tree(FORMALCONJ, FORMALCONJ_PATHS)

    sl_anums = {m.group(0) for p in sl_paths for m in [ANUM_IN_PATH.search(p)] if m}
    # A non-empty check would pass a corpus that had been half-renamed, leaving
    # the queried A-number outside the shape this probe knows how to read. The
    # count is compared against the measured one instead.
    if len(sl_anums) < SEQUENCELIB_ANUMS * 0.8:
        raise Failure(f"{SEQUENCELIB} exposes {len(sl_anums)} A-numbers in paths against "
                      f"roughly {SEQUENCELIB_ANUMS} expected; its layout changed and a "
                      "miss would mean nothing")
    sl_max = max(sl_anums)
    sl_named = sum(1 for p in sl_paths if CONCEPT_MODULE.match(p))

    fc_index = {m.group(1): p for p in fc_paths for m in [FC_OEIS.match(p)] if m}
    # KNOWN LIMIT, recorded rather than papered over: a size comparison catches a
    # wholesale rename but not a small migration. Moving two files out of
    # FormalConjectures/OEIS/ leaves 225 of 227 and passes this check, while a
    # query for one of those two now reports no indexed path. Detecting that
    # needs per-query evidence that the corpus was searched in the shape the
    # query assumes, which this probe does not have. The RESULT block's refusal
    # to claim absence is what carries the risk in the meantime.
    if len(fc_index) < FORMALCONJ_OEIS * 0.8:
        raise Failure(f"{FORMALCONJ} exposes {len(fc_index)} OEIS statements against "
                      f"roughly {FORMALCONJ_OEIS} expected; its layout changed and a "
                      "miss would mean nothing")

    hits = 0
    above_range = 0

    for anum in anums:
        bare = anum[1:].lstrip("0") or "0"
        print(f"\n=== {anum} ===")

        print(f"--- {SEQUENCELIB} ---")
        found = [p for p in sl_paths if p == f"{anum}.lean" or p.endswith(f"/{anum}.lean")]
        if found:
            for p in found:
                if p.startswith("Sequencelib/Synthetic/"):
                    note = "machine-synthesised DEFINITION, not a proof"
                elif p.startswith("Sequencelib/AISynth/"):
                    note = "AI-synthesised DEFINITION, not a proof"
                else:
                    note = "curated definition"
                print(f"HIT  {p}  [{note}]")
            hits += 1
        elif anum > sl_max:
            print(f"NO SIGNAL  above this corpus range (highest indexed {sl_max}); "
                  "a miss here means nothing")
            above_range += 1
        else:
            print(f"no indexed path  (range A000004..{sl_max}; {sl_named} concept-named")
            print("                 modules carry A-numbers only in contents and are not searched)")

        print(f"--- {FORMALCONJ} ---")
        if bare in fc_index:
            print(f"HIT  {fc_index[bare]}  [open `sorry` statement: written down, not settled]")
            hits += 1
        else:
            print(f"no indexed path  ({len(fc_index)} OEIS statements indexed)")

        print(f"--- {LEANPROOFS} ---")
        print("UNKNOWN  no A-number appears in any path of this repository; its file")
        print("         tree cannot answer the question. Not evidence of absence.")

    print()
    if hits:
        print(f"RESULT hits={hits} -- read them before dispatching")
        return 3
    print("RESULT no matching indexed path in any corpus searched.")
    print("       This does NOT establish absence and does NOT establish novelty:")
    print(f"       {LEANPROOFS} is not searchable by path at all (UNKNOWN);")
    print(f"       {sl_named} concept-named sequencelib modules are not searched;")
    if above_range:
        print(f"       {above_range} of the queries sit above the sequencelib range (NO SIGNAL).")
    print("       Literature outside these three repositories is not consulted here.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except Failure as exc:
        print(f"oeis-prior-art: {exc}", file=sys.stderr)
        sys.exit(2)
    except Exception as exc:               # noqa: BLE001 - deliberate catch-all
        # An unexpected shape or an I/O error must still be a loud failure with
        # the documented exit code, never a traceback that a caller might read
        # as something other than "this probe could not answer".
        print(f"oeis-prior-art: unexpected failure: {type(exc).__name__}: {exc}",
              file=sys.stderr)
        sys.exit(2)
