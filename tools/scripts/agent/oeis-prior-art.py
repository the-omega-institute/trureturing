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
import tempfile
from pathlib import Path

ANUM = re.compile(r"\A[0-9]{6}\Z")
ANUM_IN_PATH = re.compile(r"A[0-9]{6}")
CONCEPT_MODULE = re.compile(r"\ASequencelib/[A-Z][A-Za-z]+\.lean\Z")
FC_OEIS = re.compile(r"\AFormalConjectures/OEIS/([0-9]+)\.lean\Z")

SEQUENCELIB = os.environ.get("OEIS_SEQUENCELIB_REPO", "provables/sequencelib")
FORMALCONJ = os.environ.get("OEIS_FORMALCONJ_REPO", "google-deepmind/formal-conjectures")
LEANPROOFS = os.environ.get("OEIS_LEANPROOFS_REPO", "plby/lean-proofs")

# A cache is trusted only if it carries this marker, written by this version
# after a validated fetch. A file left by any other writer — a partial
# extraction, an older implementation, a hand-made fixture — is refetched
# rather than believed.
CACHE_MARKER = "# oeis-prior-art cache v2; validated untruncated tree\n"


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


def cache_dir() -> Path:
    raw = os.environ.get("OEIS_PRIOR_ART_CACHE") or os.path.join(
        tempfile.gettempdir(), "oeis-prior-art"
    )
    path = Path(raw)
    path.mkdir(parents=True, exist_ok=True)
    return path


def ttl_minutes() -> int:
    raw = os.environ.get("OEIS_PRIOR_ART_TTL_MIN", "720")
    if not raw.isdigit():
        raise Failure(f"OEIS_PRIOR_ART_TTL_MIN must be a whole number of minutes, got: {raw!r}")
    return int(raw)


def fetch_tree(repo: str, min_paths: int) -> list[str]:
    """Return every path in a repository's default-branch tree.

    Fails closed on a truncated tree, on a short tree, and on any cache whose
    provenance marker is absent: a truncated or partial tree turns every miss
    into a false negative, which is the single failure this probe exists to
    prevent.
    """
    import time

    slug = repo.replace("/", "_")
    if slug == repo or not slug:
        raise Failure(f"could not derive a cache slug for {repo!r}")
    cached = cache_dir() / f"{slug}.paths"

    if cached.is_file():
        age_min = (time.time() - cached.stat().st_mtime) / 60.0
        if age_min < ttl_minutes():
            text = cached.read_text()
            if text.startswith(CACHE_MARKER):
                paths = text[len(CACHE_MARKER):].splitlines()
                if len(paths) >= min_paths:
                    return paths
            # falls through to refetch: unmarked, or shorter than the corpus
            # is known to be. Never trusted on line count alone.

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

    paths = [entry["path"] for entry in tree["tree"]]
    if len(paths) < min_paths:
        raise Failure(f"{repo} yielded {len(paths)} paths, fewer than the "
                      f"{min_paths} this corpus is known to hold; refusing to trust it")

    tmp = cached.with_suffix(".partial")
    tmp.write_text(CACHE_MARKER + "\n".join(paths) + "\n")
    tmp.replace(cached)          # publish atomically, only after validation
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

    # Environment is validated up front too, so a bad TTL or an unusable cache
    # directory fails before any query rather than at the first cache hit.
    ttl_minutes()
    cache_dir()

    sl_paths = fetch_tree(SEQUENCELIB, 20000)
    fc_paths = fetch_tree(FORMALCONJ, 1000)

    sl_anums = {m.group(0) for p in sl_paths for m in [ANUM_IN_PATH.search(p)] if m}
    if not sl_anums:
        raise Failure(f"no A-number occurs in any {SEQUENCELIB} path; its layout changed")
    sl_max = max(sl_anums)
    sl_named = sum(1 for p in sl_paths if CONCEPT_MODULE.match(p))

    fc_index = {m.group(1): p for p in fc_paths for m in [FC_OEIS.match(p)] if m}
    if not fc_index:
        raise Failure(f"no FormalConjectures/OEIS/<decimal>.lean path occurs in "
                      f"{FORMALCONJ}; its layout changed and a miss would mean nothing")

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
