#!/usr/bin/env python3
"""Finite ternary-code geometry check; no hypothetical covering system is enumerated.

Success requires a prefix-free partition of all 135 admissible depth-five cells,
with the stated terminal roots, short-word assignments, and a shared mod-27 parent for one short and one long leaf.
The constructor uses natural-number congruence classes. The verifier independently
expands little-endian ternary words and checks every cell's exact multiplicity.
"""
import argparse
import hashlib
import itertools
import json
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

Q = 113
SHORT_DIGITS = (3, 4, 5, 6, 7, 8)
Q_TERMINAL_DIGIT = 0
THREE_Q_TERMINAL_DIGIT = 1
LONG_DONOR_DIGIT = 9
FORBIDDEN_GAMMA_DIGIT = 2
POW3 = tuple(3**d for d in range(6))


@dataclass(frozen=True)
class Leaf:
    digit: int
    depth: int
    residue: int


def integer_cells(depth, residue):
    return {residue + t * POW3[depth] for t in range(POW3[5-depth])}


def ternary_digits(value, depth):
    result = []
    for _ in range(depth):
        result.append(value % 3)
        value //= 3
    if value:
        raise AssertionError("noncanonical residue")
    return tuple(result)


def construct(a, b, beta_root, z, other_words):
    safe = tuple(w for w in range(9) if w % 3 != a and w != b)
    compatible = tuple(v for v in safe if v % 3 == beta_root and v != z)
    if not compatible:
        raise AssertionError("no compatible terminal word different from z")
    v = compatible[0]
    leaves = [Leaf(Q_TERMINAL_DIGIT, 3, v),
              Leaf(THREE_Q_TERMINAL_DIGIT, 4, v+9),
              Leaf(SHORT_DIGITS[0], 4, z),
              Leaf(LONG_DONOR_DIGIT, 5, z+27)]
    occupied = set()
    for leaf in leaves:
        cells = integer_cells(leaf.depth, leaf.residue)
        if cells & occupied:
            raise AssertionError("reserved-node collision")
        occupied |= cells
    for digit, word in zip(SHORT_DIGITS[1:], other_words):
        for r in range(word, 81, 9):
            cells = integer_cells(4, r)
            if not cells & occupied:
                leaves.append(Leaf(digit, 4, r))
                occupied |= cells
                break
        else:
            raise AssertionError("prescribed word has no unoccupied depth-four slot")
    free = tuple(x for x in range(243) if x % 9 in safe and x not in occupied)
    unused_digits = tuple(d for d in range(Q) if d not in {l.digit for l in leaves})
    if len(free) != len(unused_digits):
        raise AssertionError("long-leaf/digit counts differ")
    leaves.extend(Leaf(d, 5, x) for d, x in zip(unused_digits, free))
    return safe, v, tuple(leaves), len(compatible)


def verify(a, b, beta_root, z, other_words, safe, v, leaves):
    # No constructor occupancy set is consumed here.
    if len(safe) != 5 or set(safe) != {w for w in range(9) if w % 3 != a and w != b}:
        raise AssertionError("wrong five-word domain")
    indexed = {l.digit: l for l in leaves}
    if len(indexed) != len(leaves) or set(indexed) != set(range(113)):
        raise AssertionError("digits do not biject the 113 leaves")
    if Counter(l.depth for l in leaves) != {3: 1, 4: 7, 5: 105}:
        raise AssertionError("wrong depth inventory")
    q_leaf, tq_leaf = indexed[0], indexed[1]
    if q_leaf.depth != 3 or tq_leaf.depth != 4:
        raise AssertionError("wrong terminal depths")
    if not (q_leaf.residue % 9 == tq_leaf.residue % 9 == v and v != z and v in safe):
        raise AssertionError("wrong common terminal word")
    if tq_leaf.residue % 3 != beta_root:
        raise AssertionError("3q terminal misses its prescribed actual ternary root")
    expected_words = (z,) + other_words
    for digit, word in zip(SHORT_DIGITS, expected_words):
        leaf = indexed[digit]
        if leaf.depth != 4 or leaf.residue % 9 != word:
            raise AssertionError("short leaf misses its prescribed word")
    c_leaf, d_leaf = indexed[SHORT_DIGITS[0]], indexed[LONG_DONOR_DIGIT]
    if d_leaf.depth != 5 or d_leaf.residue % 9 != z:
        raise AssertionError("donor is not a long leaf in the target word")
    if c_leaf.residue % 27 != d_leaf.residue % 27:
        raise AssertionError("c and d do not share their mod-27 parent")
    if c_leaf.residue == d_leaf.residue:
        raise AssertionError("c and d are not distinct leaves")
    if len(SHORT_DIGITS) != len(set(SHORT_DIGITS)) or FORBIDDEN_GAMMA_DIGIT in SHORT_DIGITS:
        raise AssertionError("forbidden digit appears among six distinct short digits")
    if indexed[FORBIDDEN_GAMMA_DIGIT].depth != 5:
        raise AssertionError("representative forbidden digit is not long")
    continuing = tuple(l for l in leaves if l.digit not in {0, 1})
    if len(leaves) != 135-8-2-12 or len(continuing) != 111:
        raise AssertionError("wrong total or continuing count")
    expected = {ternary_digits(w, 2)+tail
                for w in safe for tail in itertools.product(range(3), repeat=3)}
    multiplicities = Counter()
    for leaf in leaves:
        if not 0 <= leaf.residue < POW3[leaf.depth]:
            raise AssertionError("leaf residue outside its canonical modulus")
        prefix = ternary_digits(leaf.residue, leaf.depth)
        for tail in itertools.product(range(3), repeat=5-leaf.depth):
            multiplicities[prefix+tail] += 1
    if set(multiplicities) != expected:
        raise AssertionError("forest has a hole or leaves the admissible domain")
    if len(expected) != 135 or set(multiplicities.values()) != {1}:
        raise AssertionError("overlapping prefix nodes or wrong full-cell count")


def cases(mode):
    phase_pairs = [(0, 1)] if mode == "canonical" else [
        (a, b) for a in range(3) for b in range(9) if b % 3 != a]
    for a, b in phase_pairs:
        safe = tuple(w for w in range(9) if w % 3 != a and w != b)
        for beta_root in range(3):
            if beta_root == a:
                continue
            for z in safe:
                for others in itertools.product(safe, repeat=5):
                    yield a, b, beta_root, z, others


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("canonical", "all-phases"), required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    started = time.perf_counter()
    count = 0
    terminal_choices = Counter()
    phase_cases = Counter()
    transcript_hash = hashlib.sha256()
    examples = []
    failure = None
    for case in cases(args.mode):
        a, b, beta_root, z, others = case
        try:
            safe, v, forest, compatible_count = construct(*case)
            verify(*case, safe, v, forest)
        except AssertionError as error:
            failure = {"case": case, "error": str(error)}
            break
        count += 1
        terminal_choices[compatible_count] += 1
        phase_cases[(a, b, beta_root)] += 1
        transcript_hash.update(json.dumps(
            [case, v, [[l.digit, l.depth, l.residue] for l in forest]],
            separators=(",", ":")).encode())
        if len(examples) < 3:
            examples.append({"case": case, "terminal_word": v,
                             "designated_leaves": [l.__dict__ for l in forest[:9]]})
    expected_count = 31250 if args.mode == "canonical" else 562500
    if failure is None and count != expected_count:
        failure = {"error": "case enumeration incomplete", "expected": expected_count, "actual": count}
    report = {
        "status": "PASS" if failure is None else "FAIL",
        "scope": "Finite ternary-code geometry only; neither Lean verification nor a theorem about existence or exclusion of an odd-distinct covering system.",
        "mode": args.mode,
        "domain": {"pure3_root_count": 1 if args.mode == "canonical" else 3,
                   "actual_pure3_pure9_phase_pairs": 1 if args.mode == "canonical" else 18,
                   "compatible_3q_roots_per_pair": 2,
                   "safe_words_per_pair": 5,
                   "shared_word_choices": 5,
                   "other_ordered_short_word_assignments": 3125},
        "completed_configurations": count,
        "expected_configurations": expected_count,
        "checked_depth5_cells": count*135,
        "distinct_phase_root_triples": len(phase_cases),
        "configurations_per_phase_root_triple": sorted(set(phase_cases.values())),
        "available_terminal_word_count_histogram": dict(sorted(terminal_choices.items())),
        "leaf_inventory_every_configuration": {"q_terminal_depth3": 1, "3q_terminal_depth4": 1,
                                               "short_depth4": 6, "long_depth5": 105,
                                               "total": 113, "continuing": 111},
        "checks": ["both terminal depths", "common safe terminal word distinct from z",
                   "3q terminal actual root", "six distinct prescribed short digits and words",
                   "short c and long d share mod27 parent", "all 113 digit labels exactly once",
                   "135 admissible full cells covered exactly once", "prefix-free initial forest",
                   "forbidden gamma outside six short digits"],
        "label_convention": "q digit labels 0,1 are terminals; 3..8 are fixed distinct short digits c,s0,s1,s2,s3,s4; d=9 is a fixed distinct long donor; gamma=2 is a representative outside this six-set. The gamma exclusion is a supplied U-domain premise, not deduced from a covering system.",
        "normalization": "canonical mode checks pure3 root0 and pure9 word1 only; all-phases mode enumerates every admissible actual pair and assumes no normalization theorem.",
        "failure": failure,
        "wall_seconds": round(time.perf_counter()-started, 6),
        "construction_stream_sha256": transcript_hash.hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "examples": examples,
    }
    Path(args.output).write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({k: report[k] for k in ("status", "mode", "completed_configurations",
                     "checked_depth5_cells", "wall_seconds", "failure")}))
    return 0 if failure is None else 1


if __name__ == "__main__":
    raise SystemExit(main())
