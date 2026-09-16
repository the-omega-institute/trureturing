#!/usr/bin/env python3
"""Exact 36-vertex bounds for the actual two-prime layout Gamma.

This checks the rational maximization after the two-root compatibility
argument. It includes the branch with no forbidden modulus-3 class.
It does not certify the mathematical reduction in Lean, and these bounds
do not replace R or the sum of separate lcm-cylinder maxima.
Python 3.9+ standard library only; no residue search or solver is used.
"""

from fractions import Fraction as F
from itertools import product
import json


EXPECTED = {
    5: (F(57, 4), F(215, 24)),
    7: (F(123, 13), F(208, 33)),
    11: (F(181, 25), F(73, 15)),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify_bound(q):
    require(q in EXPECTED, "the fixed certificate covers only q=5,7,11")
    expected_gamma, expected_absent = EXPECTED[q]
    y = F(1, q - 1)
    a_q = F(3 * q - 1, (q - 1) ** 2)
    records, denominators = [], []

    # For each selected-root branch, transfer all higher mixed deletion to
    # the other root, then enlarge it to y/6. The denominator stays positive.
    # Both objectives are linear-fractional in each of these three groups.
    for (w, v), (alpha, beta), z in product(
            ((F(1, 2), F(1)), (F(1), F(1, 2)), (F(1), F(1))),
            ((F(0), F(0)), (y, F(0)), (F(0), y)),
            (1 - y, F(1))):
        x = (w + v) / 3
        n = w * (z - alpha) / 3
        m = v * (z - beta) / 3 - y / 6
        require(n >= (1 - 2 * y) / 6 > 0,
                "selected-root density lower bound failed")
        require(m >= (1 - 3 * y) / 6 > 0,
                "other-root density lower bound failed")
        denominator = n + m
        denominators.append(denominator)

        # Root compatibility bounds the pure-ternary test-square terms by
        # 3*n + max(z-alpha, 2*(z-beta)/3). The remaining q-lcm groups
        # contribute at most a_q*x + 2*a_q, retaining every cofactor.
        for branch, extra in (
                ("selected_root", z - alpha),
                ("other_root", F(2, 3) * (z - beta))):
            gamma = 1 + (3 * n + extra + a_q * x + 2 * a_q) / denominator
            require(gamma <= expected_gamma,
                    "a present-modulus-3 vertex exceeds the claimed bound")
            records.append((gamma, branch, (w, v, alpha, beta, z)))

    require(len(denominators) == 18, "expected eighteen parameter vertices")
    require(len(records) == 36, "expected two branches at every vertex")
    present_gamma = max(value for value, _, _ in records)
    require(present_gamma == expected_gamma,
            "the present-modulus-3 maximum differs from the exact claim")

    # If modulus 3 is absent, pure ternary survivor density x is >=5/6.
    # The unsplit objective decreases in x and z, so use their lower bounds.
    x, z = F(5, 6), 1 - y
    absent_denominator = x * z - y / 2
    require(absent_denominator > 0,
            "the absent-modulus-3 denominator is not positive")
    absent_gamma = 1 + (2 * z + a_q * x + 2 * a_q) / absent_denominator
    require(absent_gamma == expected_absent,
            "the absent-modulus-3 value differs from the exact claim")
    require(absent_gamma <= present_gamma,
            "the absent-modulus-3 branch exceeds the claimed uniform bound")

    return {
        "q": q,
        "vertex_count": len(records),
        "gamma_bound": str(max(present_gamma, absent_gamma)),
        "minimum_vertex_denominator": str(min(denominators)),
        "absent_modulus_3_gamma_bound": str(absent_gamma),
        "absent_modulus_3_denominator": str(absent_denominator),
        "maximizers": [
            {"branch": branch, "w_v_alpha_beta_z": list(map(str, parameters))}
            for value, branch, parameters in records if value == present_gamma
        ],
    }


def main():
    results = [verify_bound(q) for q in (5, 7, 11)]
    require(sum(result["vertex_count"] for result in results) == 108,
            "expected 108 checked objective values across the three primes")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
