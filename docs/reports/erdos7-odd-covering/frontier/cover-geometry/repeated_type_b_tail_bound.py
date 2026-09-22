#!/usr/bin/env python3
"""Exact seed and tail bounds for repeated type-B sources.

The default verifies the specified two-digit /989 law, its prefix maxima,
the later-digit caps, and finite certificates for every positive pair of
heights H,K. It reuses the full independent-layout oracle in the sibling
height_two_layout_second_moment.py. Requires NumPy through that oracle.

The pure finite_bound, strip_bound and infinite_bound functions evaluate
the same formulas for supplied exact nonnegative seed coefficients and
caps below one. Applying those formulas to another source requires a
separate proof of its seed bound and prefix/tail mass bounds.

These are exact arithmetic checks of an ordinary proof, not Lean
certification, a minimax claim, or a realization by an actual odd cover.
"""

from fractions import Fraction
import importlib.util
from itertools import islice, product
import json
from math import prod
from pathlib import Path
import sys

import numpy as np

# Resolve this explicit sibling dependency also when Python uses -I.
_spec = importlib.util.spec_from_file_location(
    "height_two_layout_second_moment",
    Path(__file__).resolve().with_name("height_two_layout_second_moment.py"))
_oracle_module = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _oracle_module
_spec.loader.exec_module(_oracle_module)
HeightTwoLayoutOracle = _oracle_module.HeightTwoLayoutOracle
ROOT_B = _oracle_module.ROOT_B


def check(condition, message):
    if not condition:
        raise ValueError(message)


def _parameters(seed_bound, ca, cb, g, alpha, beta, gamma):
    values = (seed_bound, ca, cb, g, alpha, beta, gamma)
    check(all(type(v) in (int, Fraction) for v in values),
          "parameters must be exact integers or Fractions")
    values = tuple(Fraction(v) for v in values)
    check(all(v >= 0 for v in values), "parameters must be nonnegative")
    check(all(v < 1 for v in values[4:]), "tail caps must be less than one")
    return values


def _height(height):
    check(type(height) is int and height >= 2, "height must be an integer at least two")


def _finite_series(n, z):
    return sum(((2 * i + 5) * z**i for i in range(1, n + 1)), Fraction(0))


def _infinite_series(z):
    return 2 * z / (1 - z)**2 + 5 * z / (1 - z)


def finite_bound(height_p, height_q, *, seed_bound, ca, cb, g, alpha, beta, gamma):
    """Evaluate the two finite tail sums at literal heights >= 2."""
    _height(height_p)
    _height(height_q)
    seed_bound, ca, cb, g, alpha, beta, gamma = _parameters(
        seed_bound, ca, cb, g, alpha, beta, gamma)
    n, m = height_p - 2, height_q - 2
    joint = sum(((2 * i + 5) * (2 * j + 5) * gamma**min(i, j)
                 * alpha**max(i - j, 0) * beta**max(j - i, 0)
                 for i, j in product(range(1, n + 1), range(1, m + 1))), Fraction(0))
    return (seed_bound + ca * _finite_series(n, alpha)
            + cb * _finite_series(m, beta) + g * joint)


def strip_bound(short_height, short_axis, *, seed_bound, ca, cb, g, alpha, beta, gamma):
    """One finite coordinate height and the other coordinate unbounded.

    short_axis is 'p' or 'q'; swapping axes also swaps the coefficients
    and marginal caps. The joint sum is finite after geometric summation.
    """
    _height(short_height)
    check(short_axis in ("p", "q"), "short axis must be p or q")
    seed_bound, ca, cb, g, alpha, beta, gamma = _parameters(
        seed_bound, ca, cb, g, alpha, beta, gamma)
    if short_axis == "q":
        ca, cb, alpha, beta = cb, ca, beta, alpha
    n = short_height - 2
    joint = Fraction(0)
    for i in range(1, n + 1):
        lower = sum(((2 * j + 5) * gamma**j * alpha**(i - j)
                     for j in range(1, i + 1)), Fraction(0))
        upper = gamma**i * ((2 * i + 5) * beta / (1 - beta)
                            + 2 * beta / (1 - beta)**2)
        joint += (2 * i + 5) * (lower + upper)
    return (seed_bound + ca * _finite_series(n, alpha)
            + cb * _infinite_series(beta) + g * joint)


def infinite_bound(*, seed_bound, ca, cb, g, alpha, beta, gamma):
    """Evaluate the exact limit of the nonnegative two-tail bound."""
    seed_bound, ca, cb, g, alpha, beta, gamma = _parameters(
        seed_bound, ca, cb, g, alpha, beta, gamma)
    u = (4 * gamma * (1 + gamma) / (1 - gamma)**3
         + 20 * gamma / (1 - gamma)**2 + 25 * gamma / (1 - gamma))
    joint = (u * (1 + alpha / (1 - alpha) + beta / (1 - beta))
             + 2 * _infinite_series(gamma)
             * (alpha / (1 - alpha)**2 + beta / (1 - beta)**2))
    return (seed_bound + ca * _infinite_series(alpha)
            + cb * _infinite_series(beta) + g * joint)


def comparison_factor(height):
    check(type(height) is int and height >= 1, "comparison height must be positive")
    return 3 - Fraction(height + 2, 3**height)


def _projected_seed_maximum(oracle, weights, hp, hq):
    """Direct enumeration for the three smaller projected seed rectangles."""
    check((hp, hq) in ((1, 1), (1, 2), (2, 1)), "unsupported projected seed heights")
    w, denominator = oracle.weights(weights)
    moduli = [5**a * 7**b for a, b in product(range(hp + 1), range(hq + 1))
              if (a, b) != (0, 0)]
    residues = [oracle.residues[d] for d in moduli]
    choices = product(*residues)
    best, witness, count = -1, None, 0
    while True:
        chunk = list(islice(choices, 1024))
        if not chunk:
            break
        phases = np.array(chunk, dtype=np.int64)
        count += len(chunk)
        load = np.ones((len(chunk), len(w)), dtype=np.int64)
        for j, d in enumerate(moduli):
            load += oracle.point_residues[d][None, :] == phases[:, j, None]
        costs = (load * load * w).sum(axis=1)
        j = int(costs.argmax())
        if int(costs[j]) > best:
            best = int(costs[j])
            witness = {1: 0, **dict(zip(moduli, map(int, phases[j])))}
    check(count == prod(map(len, residues)), "every projected seed layout must be visited")
    literal = np.ones(len(w), dtype=np.int64)
    for d in moduli:
        literal += oracle.point_residues[d] == witness[d]
    check(int(np.dot(literal * literal, w)) == best, "projected literal attaining witness")
    return dict(height_p=hp, height_q=hq, exact_maximum=str(Fraction(best, denominator)),
                layouts=count, attaining_layout={str(d): a for d, a in witness.items()})


def verify():
    matrix = ((35, 16, 30), (24, 10, 21), (32, 14, 27))
    kinds = [0 if x == 1 else 1 if y == 2 else 2 for x, y in ROOT_B]
    points = [(u[0] + 5 * v[0], u[1] + 7 * v[1])
              for u, v in product(ROOT_B, repeat=2)]
    weights = [matrix[kinds[i]][kinds[j]] for i, j in product(range(7), repeat=2)]
    check(sum(weights) == 989, "the seed law must normalize with denominator 989")
    oracle = HeightTwoLayoutOracle(5, 7, points)
    seed = oracle.separate(weights)
    check(seed.value == Fraction(5989, 989), "full independent seed maximum")
    check(seed.baseline_choices == 56000, "all seed baselines must be examined")

    prefix = {}
    expected_prefix = ((989, 351, 90), (272, 173, 48), (72, 46, 35))
    for a, b in product(range(3), repeat=2):
        masses = {}
        for (x, y), weight in zip(points, weights):
            cell = x % 5**a, y % 7**b
            masses[cell] = masses.get(cell, 0) + weight
        prefix[a, b] = Fraction(max(masses.values()), 989)
        check(prefix[a, b] == Fraction(expected_prefix[a][b], 989), "exact prefix maximum")
    ca = sum((2 * b + 1) * prefix[2, b] for b in range(3))
    cb = sum((2 * a + 1) * prefix[a, 2] for a in range(3))
    g = prefix[2, 2]
    check((ca, cb, g) == (Fraction(385, 989), Fraction(409, 989), Fraction(35, 989)),
          "seed side coefficients")

    tail = [Fraction(1, 15) if kind == 1 else Fraction(1, 5) for kind in kinds]
    check(sum(tail) == 1, "the later-digit law must normalize")
    alpha = max(sum(w for (x, y), w in zip(ROOT_B, tail) if x == a) for a in range(5))
    beta = max(sum(w for (x, y), w in zip(ROOT_B, tail) if y == b) for b in range(7))
    gamma = max(tail)
    check((alpha, beta, gamma) == (Fraction(4, 15), Fraction(1, 5), Fraction(1, 5)),
          "the tail row, column and atom caps")
    params = dict(seed_bound=seed.value, ca=ca, cb=cb, g=g,
                  alpha=alpha, beta=beta, gamma=gamma)
    limit = infinite_bound(**params)
    check(limit == Fraction(67803771, 7658816), "exact infinite bound")
    large_target = comparison_factor(6)**2
    check(limit < large_target < 9, "the quadrant with both heights at least six")

    finite_cells = []
    for hp, hq in product(range(2, 5), repeat=2):
        bound = finite_bound(hp, hq, **params)
        target = comparison_factor(hp) * comparison_factor(hq)
        check(bound < target, "finite small-height comparison")
        finite_cells.append(dict(height_p=hp, height_q=hq, bound=str(bound),
                                 target=str(target), margin=str(target - bound)))
    strips = []
    for axis, height in product(("p", "q"), range(2, 6)):
        bound = strip_bound(height, axis, **params)
        target = comparison_factor(height) * comparison_factor(5)
        check(bound < target, "unbounded strip comparison")
        strips.append(dict(short_axis=axis, short_height=height, bound=str(bound),
                           target=str(target), margin=str(target - bound)))
    diagonal = []
    for height in range(2, 7):
        bound = finite_bound(height, height, **params)
        target = comparison_factor(height)**2
        check(bound < target, "equal-height comparison")
        diagonal.append(dict(height=height, bound=str(bound), target=str(target),
                             margin=str(target - bound)))
    boundary = []
    for hp, hq, numerator, count in ((1, 1, 3911, 140), (1, 2, 4811, 122500),
                                    (2, 1, 4740, 62720)):
        row = _projected_seed_maximum(oracle, weights, hp, hq)
        check(Fraction(row["exact_maximum"]) == Fraction(numerator, 989),
              "projected seed maximum")
        check(row["layouts"] == count, "projected layout count")
        target = comparison_factor(hp) * comparison_factor(hq)
        check(Fraction(numerator, 989) < target, "projected finite target")
        row.update(target=str(target), margin=str(target - Fraction(numerator, 989)))
        if (hp, hq) != (1, 1):
            coefficient = (prefix[0, 2] + 3 * prefix[1, 2] if hp == 1
                           else prefix[2, 0] + 3 * prefix[2, 1])
            cap = beta if hp == 1 else alpha
            boundary_limit = Fraction(numerator, 989) + coefficient * _infinite_series(cap)
            expected = Fraction(913, 172) if hp == 1 else Fraction(644940, 119669)
            check(boundary_limit == expected, "one-coordinate boundary limit")
            cutoff_target = 2 * comparison_factor(3)
            check(boundary_limit < cutoff_target, "all other boundary heights at least three")
            row.update(tail_coefficient=str(coefficient), tail_cap=str(cap),
                       infinite_bound=str(boundary_limit), cutoff_target=str(cutoff_target),
                       cutoff_margin=str(cutoff_target - boundary_limit))
        boundary.append(row)
    return dict(
        scope="Specified repeated type-B source and one compatible law; every independent divisor layout; all positive heights H,K",
        weight_matrix=matrix, weight_denominator=989, seed=seed.output(),
        prefix_numerators=expected_prefix, prefix_denominator=989,
        parameters={key: str(value) for key, value in params.items()},
        infinite_bound=str(limit), nine_minus_limit=str(9 - limit),
        large_quadrant_target=str(large_target), large_quadrant_margin=str(large_target - limit),
        finite_cells=finite_cells, strips=strips, diagonal=diagonal, boundary=boundary,
    )


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
