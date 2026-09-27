#!/usr/bin/env python3
"""Finite original-AP countercontrol to the proposed 14/79 three-color cap.

Only Python's standard library is used. The two main counts are independent:
one uses unit-digit support patterns; the other decodes the actual CRT labels,
retains each valuation separately, and counts their literal cylinder union.
No claim of a covering system or an infinite-height theorem is made.
"""

import argparse
import json
from fractions import Fraction
from itertools import product
from math import prod
from pathlib import Path


PRIMES = (5, 7, 11, 13)
HEIGHT = 3
THRESHOLD = Fraction(14, 79)
OLD = {
    1: (1,), 2: (1,), 4: (1,), 8: (1,),
    3: (3, 3), 5: (4, 3), 9: (4, 3), 6: (4, 4),
    10: (5, 4), 12: (5, 5), 7: (3, 6, 6), 11: (3, 6, 6),
    13: (4, 6, 6), 14: (6, 7, 7), 15: (3, 6, 8, 8),
}
NEW = {
    1: (0, (2,)), 2: (1, (2,)), 4: (2, (2,)), 8: (2, (2,)),
    3: (2, (2, 2)), 5: (1, (2, 2)), 9: (1, (2, 2)),
    6: (0, (2, 2)), 10: (0, (2, 2)), 12: (0, (2, 2)),
    7: (2, (2, 2, 2)), 11: (2, (2, 2, 2)),
    13: (1, (4, 2, 2)), 14: (1, (4, 2, 2)),
    15: (1, (3, 5, 2, 2)),
}
SUPPORTS = {m: tuple(i for i in range(4) if m >> i & 1)
            for m in range(1, 16)}


def rational(value):
    return f"{value.numerator}/{value.denominator}"


def crt(congruences):
    modulus = prod(m for m, _ in congruences)
    residue = sum(a * (modulus // m) * pow(modulus // m, -1, m)
                  for m, a in congruences) % modulus
    assert all(residue % m == a for m, a in congruences)
    return [modulus, residue]


def materialize(height):
    old, new = [], []
    for mask, indices in SUPPORTS.items():
        for exponents in product(range(1, height + 1), repeat=len(indices)):
            powers = tuple(PRIMES[i] ** e for i, e in zip(indices, exponents))
            old_congruences = [(pwr, r * PRIMES[i] ** (e - 1))
                               for pwr, i, e, r in
                               zip(powers, indices, exponents, OLD[mask])]
            color, digits = NEW[mask]
            new_congruences = [(pwr, r * PRIMES[i] ** (e - 1))
                               for pwr, i, e, r in
                               zip(powers, indices, exponents, digits)]
            old.append(crt(old_congruences))
            new.append(crt([(3, color)] + new_congruences))
    old.sort()
    new.sort()
    return old, new


def compressed_count(height):
    """First-nonzero-digit cells, using support patterns directly."""
    weights = [(q ** height - 1) // (q - 1) for q in PRIMES]
    histogram = [0] * 8
    cells = 0
    domains = [(0,) + tuple(range(2, q)) for q in PRIMES]
    for word in product(*domains):
        cells += 1
        if any(tuple(word[i] for i in SUPPORTS[m]) == pat
               for m, pat in OLD.items()):
            continue
        colors = 0
        for m, (color, pat) in NEW.items():
            if tuple(word[i] for i in SUPPORTS[m]) == pat:
                colors |= 1 << color
        weight = prod(1 if value == 0 else w for value, w in zip(word, weights))
        histogram[colors] += weight
    return histogram, cells


def decode_labels(labels, height, parent):
    """Recover all requirements from literal (modulus,residue), not OLD/NEW."""
    decoded = {m: {} for m in range(1, 16)}
    exponent_vectors = set()
    for modulus, residue in labels:
        assert 0 <= residue < modulus
        remaining = modulus
        if parent:
            assert remaining % 3 == 0 and remaining % 9 != 0
            remaining //= 3
            color = residue % 3
        else:
            assert remaining % 3 != 0
            color = None
        mask, full_exponents, requirements = 0, [], []
        for i, q in enumerate(PRIMES):
            exponent = 0
            while remaining % q == 0:
                exponent += 1
                remaining //= q
            full_exponents.append(exponent)
            assert 0 <= exponent <= height
            if exponent:
                mask |= 1 << i
                prime_power = q ** exponent
                local_residue = residue % prime_power
                low_power = q ** (exponent - 1)
                assert local_residue % low_power == 0
                digit = local_residue // low_power
                assert 1 <= digit < q
                requirements.append((exponent, digit))
        assert remaining == 1 and mask
        assert tuple(full_exponents) not in exponent_vectors
        exponent_vectors.add(tuple(full_exponents))
        key = tuple(requirements)
        assert key not in decoded[mask]
        decoded[mask][key] = color
    expected = set(product(range(height + 1), repeat=4)) - {(0, 0, 0, 0)}
    assert exponent_vectors == expected
    return decoded


def valuation_count(old_labels, new_labels, height):
    """Count literal APs on valuation-digit cells, each with its own weight.

    A decoded AP coordinate has residue r*q**(e-1) modulo q**e.
    It is exactly the state 'first nonzero digit is at e and equals r'.
    Hence every AP's indicator is constant on every enumerated cell.
    """
    all_moduli = [m for m, _ in old_labels + new_labels]
    assert len(all_moduli) == len(set(all_moduli))
    assert {m for m, _ in old_labels} == {m // 3 for m, _ in new_labels}
    old = decode_labels(old_labels, height, parent=False)
    new = decode_labels(new_labels, height, parent=True)
    axes, pure_survivors = [], []
    for i, q in enumerate(PRIMES):
        states = [((0, 0), 1)] + [((e, r), q ** (height - e))
                  for e in range(1, height + 1) for r in range(1, q)]
        assert sum(weight for _, weight in states) == q ** height
        allowed = [(state, weight) for state, weight in states
                   if (state,) not in old[1 << i]]
        axes.append(allowed)
        pure_survivors.append(sum(weight for _, weight in allowed))
    histogram, cells = [0] * 8, 0
    for cell in product(*axes):
        cells += 1
        states = tuple(state for state, _ in cell)
        weight = prod(weight for _, weight in cell)
        colors, forbidden = 0, False
        for mask, indices in SUPPORTS.items():
            key = tuple(states[i] for i in indices)
            if key in old[mask]:
                forbidden = True
                break
            if key in new[mask]:
                colors |= 1 << new[mask][key]
        if not forbidden:
            histogram[colors] += weight
    return histogram, cells, pure_survivors


def full_period_control():
    """Height-one independent sieve of every original child integer."""
    old, new = materialize(1)
    histogram = [0] * 8
    for x in range(prod(PRIMES)):
        if any(x % d == a for d, a in old):
            continue
        colors = 0
        for modulus, residue in new:
            d = modulus // 3
            if x % d == residue % d:
                colors |= 1 << (residue % 3)
        histogram[colors] += 1
    compressed, _ = compressed_count(1)
    valuation, _, _ = valuation_count(old, new, 1)
    assert histogram == compressed == valuation
    assert sum(histogram) == 2493 and histogram[7] == 291
    return {"height": 1, "child_period": prod(PRIMES),
            "survivors": sum(histogram), "triple": histogram[7],
            "survivor_color_histogram": histogram}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    old, new = materialize(HEIGHT)
    compressed, compressed_cells = compressed_count(HEIGHT)
    valuation, valuation_cells, pure_counts = valuation_count(old, new, HEIGHT)
    assert compressed == valuation
    survivors, triple = sum(valuation), valuation[7]
    ratio = Fraction(triple, survivors)
    assert survivors == 52156725189 and triple == 9255389299
    assert ratio > THRESHOLD
    child_period = prod(q ** HEIGHT for q in PRIMES)
    pure_period_survivors = prod(pure_counts)
    original_uncovered = sum((3 - mask.bit_count()) * count
                             for mask, count in enumerate(valuation))
    assert original_uncovered > 0
    result = {
        "schema": "k5-three-color-original-ap-countercontrol-v1",
        "scope": "Refutes only the uniform 14/79 three-color intersection cap; not a covering-system counterexample.",
        "child_primes": PRIMES, "child_height": HEIGHT,
        "parent_prime": 3, "parent_exponent": 1,
        "child_period": child_period, "full_period": 3 * child_period,
        "old_label_count": len(old), "new_label_count": len(new),
        "pure_axis_survivor_counts": pure_counts,
        "pure_old_survivors": pure_period_survivors,
        "complete_old_survivors": survivors,
        "complete_old_survival_given_pure": rational(Fraction(survivors, pure_period_survivors)),
        "triple_intersection": triple, "conditional_triple_probability": rational(ratio),
        "threshold": rational(THRESHOLD), "excess": rational(ratio - THRESHOLD),
        "survivor_color_histogram": valuation,
        "full_original_uncovered_count": original_uncovered,
        "compressed_cell_count": compressed_cells,
        "valuation_cell_count": valuation_cells,
        "height_one_literal_sieve_control": full_period_control(),
        "label_format": ["modulus", "least_nonnegative_residue"],
        "old_original_labels": old, "new_original_labels": new,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n")
    print(json.dumps({key: result[key] for key in (
        "complete_old_survivors", "triple_intersection", "conditional_triple_probability",
        "excess", "full_original_uncovered_count", "compressed_cell_count",
        "valuation_cell_count")}, sort_keys=True))


if __name__ == "__main__":
    main()
