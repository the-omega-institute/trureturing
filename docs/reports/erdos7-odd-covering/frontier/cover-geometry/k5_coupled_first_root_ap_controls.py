#!/usr/bin/env python3
"""Original AP controls for complete parent fibres, using no oracle residues.

Standard library only. Exact full-period integer sieve is compared pointwise
with independent complete-child sieves at every full parent word.
"""
import argparse
import json
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path


CHILD_PRIMES = (5, 7, 11, 13)
CHILD_PERIOD = prod(CHILD_PRIMES)
CHILD_DIVISORS = sorted(prod(q for q, bit in zip(CHILD_PRIMES, bits) if bit)
                        for bits in product((0, 1), repeat=4))


def crt(parent_modulus, parent_residue, child_modulus, child_residue):
    if child_modulus == 1:
        return parent_residue
    return (parent_residue + parent_modulus *
            (((child_residue-parent_residue) *
              pow(parent_modulus, -1, child_modulus)) % child_modulus))


def labels_for(height):
    labels = []
    for a in range(height+1):
        for d in CHILD_DIVISORS:
            if a == 0 and d == 1:
                continue
            m = 3**a * d
            if a == 0:
                residue = 0
            elif d == 1:
                residue = 1
            elif d == 5:
                residue = crt(3**a, 0, 5, a % 5)
            else:
                residue = 0
            assert 0 <= residue < m
            labels.append([m, residue])
    labels.sort()
    return labels


def sieve(period, classes):
    live = bytearray(b"\1") * period
    for modulus, residue in classes:
        assert period % modulus == 0 and 0 <= residue < modulus
        live[residue::modulus] = b"\0" * (period // modulus)
    return live


def decode(modulus, residue):
    parent_modulus = 1
    while modulus % 3 == 0:
        modulus //= 3
        parent_modulus *= 3
    return (parent_modulus, residue % parent_modulus,
            modulus, residue % modulus)


def minimal_prefix_cover(words, height):
    period = 3**height
    wordset = set(words)
    cover = []
    def visit(residue, modulus):
        descendants = range(residue, period, modulus)
        count = sum(x in wordset for x in descendants)
        if count == 0:
            return
        if count == period // modulus:
            cover.append([modulus, residue])
            return
        assert modulus < period
        for digit in range(3):
            visit(residue + digit * modulus, 3 * modulus)
    visit(0, 1)
    assert sum(period // m for m, _ in cover) == len(wordset)
    assert {x for m, r in cover for x in range(r, period, m)} == wordset
    return cover


def control(height):
    labels = labels_for(height)
    parent_period = 3**height
    full_period = parent_period * CHILD_PERIOD
    assert len(labels) == (height+1)*16-1
    assert len({m for m, _ in labels}) == len(labels)
    expected_moduli = {3**a * d for a in range(height+1) for d in CHILD_DIVISORS}
    assert {m for m, _ in labels} == expected_moduli - {1}
    full_live = sieve(full_period, labels)
    decoded = [decode(m, r) for m, r in labels]
    block_only_labels = [[m, r] for m, r in labels if decode(m, r)[2] > 1]
    block_only_full_live = sieve(full_period, block_only_labels)
    old_labels = [[d, b] for p, _, d, b in decoded if p == 1]
    old_live = sieve(CHILD_PERIOD, old_labels)
    old_count = sum(old_live)
    assert old_count == 2880
    pure_parent = [(p, a) for p, a, d, _ in decoded if d == 1]
    pure_allowed = [x for x in range(parent_period)
                    if not any(x % p == a for p, a in pure_parent)]
    pure_allowed_set = set(pure_allowed)
    fibre_counts = []
    block_only_fibre_counts = []
    block_only_whole_fibre_blocked = []
    whole_fibre_blocked = []
    for parent_word in range(parent_period):
        # This is a separate child sieve of literal active original labels.
        active = [[d, b] for p, a, d, b in decoded if parent_word % p == a]
        child_live = sieve(CHILD_PERIOD, active)
        block_only_child_live = sieve(CHILD_PERIOD,
                                      [[d, b] for d, b in active if d > 1])
        count = sum(child_live)
        block_count = sum(block_only_child_live)
        fibre_counts.append(count)
        block_only_fibre_counts.append(block_count)
        if block_count == 0:
            block_only_whole_fibre_blocked.append(parent_word)
        for x in range(parent_word, full_period, parent_period):
            assert bool(full_live[x]) == bool(child_live[x % CHILD_PERIOD])
            assert bool(block_only_full_live[x]) == bool(
                block_only_child_live[x % CHILD_PERIOD])
        assert count == sum(full_live[parent_word::parent_period])
        assert block_count == sum(block_only_full_live[parent_word::parent_period])
        assert count == (block_count if parent_word in pure_allowed_set else 0)
        if parent_word in pure_allowed_set and count == 0:
            whole_fibre_blocked.append(parent_word)
    assert sum(fibre_counts) == sum(full_live)
    assert sum(block_only_fibre_counts) == sum(block_only_full_live)
    block_only_cover = minimal_prefix_cover(block_only_whole_fibre_blocked, height)
    block_only_haar = sum((F(1, m) for m, _ in block_only_cover), F())
    assert block_only_haar == F(len(block_only_whole_fibre_blocked), parent_period)
    block_cover = minimal_prefix_cover(whole_fibre_blocked, height)
    full_dead_words = [r for r, count in enumerate(fibre_counts) if count == 0]
    full_dead_cover = minimal_prefix_cover(full_dead_words, height)
    block_haar = sum((F(1, m) for m, _ in block_cover), F())
    assert block_haar == F(len(whole_fibre_blocked), parent_period)
    # These are actual joint product-law row masses, not a theorem about fees.
    row_masses = []
    level_unions = {a: bytearray(CHILD_PERIOD) for a in range(1, height+1)}
    for m, residue in labels:
        p, a, d, b = decode(m, residue)
        if p == 1 or d == 1:
            continue
        hits = [x for x in range(b, CHILD_PERIOD, d) if old_live[x]]
        e = 0
        v = p
        while v > 1:
            e += 1
            v //= 3
        for x in hits:
            level_unions[e][x] = 1
        row_masses.append({
            "modulus": m, "residue": residue,
            "parent_modulus": p, "parent_residue": a,
            "child_cofactor": d, "child_residue": b,
            "old_child_hit_count": len(hits),
            "old_child_probability": str(F(len(hits), old_count)),
            "parent_haar_times_old_child_probability": str(F(len(hits), p*old_count)),
        })
    level_probabilities = {str(a): str(F(sum(v), old_count))
                           for a, v in level_unions.items()}
    weighted_row_mass = sum((F(row["parent_haar_times_old_child_probability"])
                             for row in row_masses), F())
    assert weighted_row_mass == sum((F(1, 4*3**a) for a in range(1,height+1)), F())
    assert F(sum(full_live), parent_period * old_count) == (
        F(len(pure_allowed), parent_period) - weighted_row_mass)
    expected_count = {2: 14400, 4: 126720}[height]
    expected_block = {2: [], 4: [0]}[height]
    assert sum(full_live) == expected_count
    assert whole_fibre_blocked == expected_block
    assert block_only_whole_fibre_blocked == expected_block
    assert F(sum(block_only_full_live), parent_period * old_count) == 1-weighted_row_mass
    assert all(row["old_child_hit_count"] == (720 if row["child_cofactor"] == 5 else 0)
               for row in row_masses)
    return {
        "parent_height": height, "parent_period": parent_period,
        "child_primes": CHILD_PRIMES, "child_period": CHILD_PERIOD,
        "full_original_period": full_period, "original_label_count": len(labels),
        "original_labels": labels, "label_format": ["modulus", "least_nonnegative_residue"],
        "complete_old_child_survivor_count": old_count,
        "parent_pure_allowed_words": pure_allowed,
        "parent_pure_allowed_haar": str(F(len(pure_allowed), parent_period)),
        "complete_child_survivor_count_by_parent_word": fibre_counts,
        "block_only_complete_child_survivor_count_by_parent_word": block_only_fibre_counts,
        "block_only_definition": "All old child labels and mixed parent-child labels, excluding every parent-pure label; all complete parent words are tested.",
        "block_only_blocked_words_all_parent_words": block_only_whole_fibre_blocked,
        "block_only_blocked_minimal_parent_cylinders": block_only_cover,
        "block_only_blocked_parent_haar_unconditioned": str(block_only_haar),
        "block_only_full_original_uncovered_count": sum(block_only_full_live),
        "blocked_words_inside_parent_pure_domain": whole_fibre_blocked,
        "blocked_minimal_parent_cylinders": block_cover,
        "blocked_parent_haar_unconditioned": str(block_haar),
        "blocked_parent_probability_given_pure": str(F(len(whole_fibre_blocked), len(pure_allowed))),
        "all_dead_parent_minimal_cylinders_including_parent_pure": full_dead_cover,
        "full_original_uncovered_count": sum(full_live),
        "full_original_uncovered_probability": str(F(sum(full_live), full_period)),
        "first_uncovered_original_integer": next(x for x, live in enumerate(full_live) if live),
        "new_mixed_row_masses_in_same_old_child_law": row_masses,
        "new_mixed_level_union_probabilities": level_probabilities,
        "sum_parent_haar_times_actual_old_child_row_mass": str(weighted_row_mass),
        "full_five_prime_support_label_count": height,
        "full_five_prime_support_has_zero_old_child_mass": True,
        "pointwise_full_period_vs_complete_fibre_comparison": True,
    }


def main():
    if not __debug__:
        raise RuntimeError("Assertions must be enabled; do not run with -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = {
        "scope": "Two explicit original AP controls of full parent-fibre and weighted Haar interfaces; no oracle residues, no general parent-fee theorem.",
        "construction": "All nonunit divisors of 3^H*5*7*11*13. Old child labels 0. Parent pure 3^a labels 1. Each 3^a*5 has parent residue 0 and child residue a mod5. Other mixed labels 0.",
        "controls": [control(2), control(4)],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, sort_keys=True, separators=(",", ":"))+"\n")
    print(json.dumps([{
        k: record[k] for k in (
            "parent_height", "original_label_count", "full_original_period",
            "full_original_uncovered_count", "blocked_words_inside_parent_pure_domain",
            "blocked_parent_haar_unconditioned",
            "block_only_blocked_words_all_parent_words",
            "block_only_blocked_parent_haar_unconditioned",
            "sum_parent_haar_times_actual_old_child_row_mass")
    } for record in result["controls"]], sort_keys=True))


if __name__ == "__main__":
    main()
