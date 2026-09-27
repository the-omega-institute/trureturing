#!/usr/bin/env python3
"""Verify the fixed depth-two fibre comparison's reweighting obstruction."""
import argparse
from fractions import Fraction as F
from itertools import combinations
import json
from math import prod
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pair(value):
    return [value.numerator, value.denominator]


def calculate():
    qs = (5, 7, 11, 13, 17, 19)
    groups = ((0, 1), (2, 3, 4))
    choices = ((1, 3), (0, 1), (0, 0), (0, 1), (0, 1), (0, 0))
    budgets = [F(1, q - 2) for q in qs]
    reference = (F(1, 4), F(1, 4), F(1, 4), F(0), F(1, 4))
    beta = [[budgets[i] * (int(l in groups[r]) + int(l == s))
             for l in range(5)] for i, (r, s) in enumerate(choices)]
    require(all(0 <= value < 1 for row in beta for value in row), "invalid blocked mass")
    supports = [set(d) for size in range(2, 7) for d in combinations(range(6), size)]

    def fibre(removed):
        return [prod(1 - beta[i][l] for i in range(6) if i not in removed)
                for l in range(5)]

    initial = fibre(set())
    upper = list(initial)
    uniform_mass = sum(initial) / 5
    reference_mass = sum(w * g for w, g in zip(reference, initial))
    for support in supports:
        weight = prod(budgets[i] for i in support)
        g = fibre(support)
        values = [w * x for w, x in zip(reference, g)]
        roots = [sum(values[l] for l in group) for group in groups]
        # One fixed reference determines affine lower bounds on both maxima.
        # Root ties choose index 1; leaf ties use their uniform average.
        root = max(range(2), key=lambda i: (roots[i], i))
        leaves = [l for l in range(5) if values[l] == max(values)]
        for l in range(5):
            selected = F(int(l in groups[root])) + F(int(l in leaves), len(leaves))
            upper[l] -= weight * g[l] * (1 + selected)
        uniform_mass -= weight * (sum(g) + max(sum(g[l] for l in group)
                                              for group in groups) + max(g)) / 5
        reference_mass -= weight * (sum(values) + max(roots) + max(values))

    expected = [F(309137, 1514700), F(179237, 1514700), F(-2611, 504900),
                F(-5363, 34425), F(-2611, 504900)]
    require(upper == expected, "affine mass coefficients differ")
    require(0 < upper[1] < upper[0] and max(upper[2:]) < 0, "coefficient signs differ")
    require(uniform_mass == F(6074, 210375), "uniform mass differs")
    require(reference_mass == sum(w * a for w, a in zip(reference, upper))
            == F(118177, 1514700), "reference tangency differs")

    # Only product atoms below 9 are needed. The full first moment includes
    # every geometric tail; no original prime-power height is truncated.
    limit = 8
    small = {1: F(1)}
    for q in qs:
        cap = F(q - 1, q - 2)
        pmf = {1: 1 - cap / q}
        pmf.update({n: cap * F(q - 1, q ** n) for n in range(2, limit + 1)})
        updated = {}
        for a, pa in small.items():
            for n, pn in pmf.items():
                if a * n <= limit:
                    updated[a * n] = updated.get(a * n, F(0)) + pa * pn
        small = updated

    # The scalar comparison has ternary tails 1, 1/4, 1/12, 1/36, ... .
    ternary = {2: F(3, 4)}
    ternary.update({n: F(1, 2 * 3 ** (n - 2)) for n in range(3, limit + 1)})
    atoms = {}
    for a, pa in small.items():
        for n, pn in ternary.items():
            if a * n <= limit:
                atoms[a * n] = atoms.get(a * n, F(0)) + pa * pn
    mean = F(19, 8) * prod(F(q - 1, q - 2) for q in qs)
    tail8 = 1 - sum(p for n, p in atoms.items() if n < 8)
    tail9 = 1 - sum(atoms.values())
    hinge8 = mean - 8 + sum((8 - n) * p for n, p in atoms.items() if n < 8)
    target = F(616, 51)
    coefficient = upper[0]
    score8 = (target - 8) * coefficient - hinge8
    require(tail9 < coefficient < tail8, "threshold 8 does not maximize the scalar score")
    require(score8 < F(-7, 100), "negative scalar margin failed")
    return {
        "scope": "Fixed depth-two comparison domain; no actual-family realization or Lean verification.",
        "q_primes": list(qs),
        "groups": [list(group) for group in groups],
        "choices": [list(choice) for choice in choices],
        "reference_weights": [pair(w) for w in reference],
        "support_count": len(supports),
        "mass_affine_upper_coefficients": [pair(a) for a in upper],
        "uniform_comparison_mass": pair(uniform_mass),
        "reference_comparison_mass": pair(reference_mass),
        "target_plus_one": pair(target),
        "scalar_mean": pair(mean),
        "scalar_atoms_below_nine": [[n, pair(p)] for n, p in sorted(atoms.items())],
        "scalar_tail8": pair(tail8),
        "scalar_tail9": pair(tail9),
        "left_slope_at_eight": pair(tail8 - coefficient),
        "right_slope_at_eight": pair(tail9 - coefficient),
        "scalar_hinge8": pair(hinge8),
        "scalar_maximizing_threshold": 8,
        "scalar_maximum_score": pair(score8),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = calculate()
    if args.output is None:
        expected = json.loads(Path(__file__).with_suffix(".json").read_text())
        require(result == expected, "retained result mismatch")
    else:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"verified_supports": result["support_count"],
                      "scalar_maximum_score": result["scalar_maximum_score"]}))


if __name__ == "__main__":
    main()
