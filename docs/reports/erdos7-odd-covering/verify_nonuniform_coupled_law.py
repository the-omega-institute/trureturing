#!/usr/bin/env python3
"""Exact finite certificate for the adaptive two-root survivor-law envelope.

The proof reducing the continuous domain and residue layouts to these
inequalities is in Problems/erdos-7-odd-covering-systems.md. This checks rational
inequalities, not the residue-layout correspondence or a Lean proof.
Uses only the Python standard library; safe under python -I and -O.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

import argparse
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

Y = F(1, 4)
A = F(7, 8)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def vertices():
    return list(product(
        ((F(1, 2), F(1)), (F(1), F(1, 2)), (F(1), F(1))),
        ((F(0), F(0)), (Y, F(0)), (F(0), Y)),
        (1 - Y, F(1)),
        ((F(0), F(0)), (Y / 6, F(0)), (F(0), Y / 6)),
    ))


def quantities(vertex, h, k):
    (w, v), (alpha, beta), z, (t, u) = vertex
    d, e = z - alpha, z - beta
    n, m = w * d / 3 - t, v * e / 3 - u
    total, x = h * n + k * m, (h * w + k * v) / 3
    root_a = (h * (w + 1), h * w + F(2, 3) * k)
    root_b = (k * (v + 1), k * v + F(2, 3) * h)
    pure_a = (3 * h * n + h * d, 3 * h * n + F(2, 3) * k * e)
    pure_b = (3 * k * m + k * e, 3 * k * m + F(2, 3) * h * d)
    gamma_numerators = [
        p + A * x + Y * q + (A - Y) * b
        for pure, root in ((pure_a, root_a), (pure_b, root_b))
        for p, q, b in product(pure, root, root_a + root_b)
    ]
    r_numerators = [
        root + cap / 6 + Y * (x + mixed / 3 + top / 6)
        for root, cap, mixed, top in product(
            (h * n, k * m), (h * d, k * e),
            (h * w, k * v), (h, k),
        )
    ]
    return n, m, total, gamma_numerators, r_numerators


def gamma_margins(vertex, gamma_cap, h, k):
    _, _, total, nums, _ = quantities(vertex, h, k)
    return [(gamma_cap - 1) * total - num for num in nums]


def propagate(gamma_cap, r_cap, prime):
    loss = r_cap / (prime - 2)
    require(loss < 1, "Propagation requires positive surviving mass")
    gamma_factor = F(prime * prime + 1, (prime - 1) * (prime - 2))
    r_factor = F(prime - 1, prime - 2)
    return ((gamma_factor * gamma_cap - loss) / (1 - loss),
            (r_factor * (r_cap + 1) - 1) / (1 - loss))


def verify(certificate):
    require(certificate["schema"] == "adaptive-two-root-coupled-v1", "Wrong schema")
    gamma_cap = F(certificate["gamma_cap"])
    r_cap = F(certificate["r_cap"])
    density_cap = F(certificate["density_cap"])
    require(gamma_cap == F(687, 50), "Wrong target Gamma")
    require(r_cap == F(37, 17), "Wrong target R")
    require(density_cap == F(16, 15), "Wrong target density")
    require(gamma_cap < F(55, 4), "No strict improvement over uniform Gamma")
    expected = certificate["expected"]
    grid = vertices()
    require(len(grid) == expected["vertices"] == 54, "Wrong vertex count")
    uniform = [gamma_margins(g, gamma_cap, F(1), F(1)) for g in grid]
    require(all(len(row) == expected["gamma_branches"] == 32 for row in uniform),
            "Wrong Gamma branch count")
    bad = [i for i in range(32) if min(row[i] for row in uniform) < 0]
    policies = certificate["policies"]
    require(bad == [0, 2, 8, 16, 18, 26], "Unexpected unsafe uniform branch")
    require([p["trigger"] for p in policies] == bad, "Incomplete or duplicate policy")
    counts = dict.fromkeys(("safe_uniform_checks", "adaptive_gamma_checks",
                           "fixed_weight_r_checks", "adaptive_density_checks"), 0)
    minimum = dict.fromkeys(counts, None)

    def check(category, margin):
        require(margin >= 0, f"Negative {category} margin: {margin}")
        counts[category] += 1
        if minimum[category] is None or margin < minimum[category]:
            minimum[category] = margin

    for row in uniform:
        for i, margin in enumerate(row):
            if i not in bad:
                check("safe_uniform_checks", margin)

    root_minimum = min(
        q for g in grid for q in quantities(g, F(1), F(1))[:2]
    )
    require(root_minimum == F(expected["minimum_root_mass"]) == F(1, 24),
            "Wrong root positivity bound")
    weights = set()
    for policy in policies:
        i = policy["trigger"]
        h, k = F(policy["h"]), F(policy["k"])
        require(h > 0 and k > 0, "Nonpositive weights")
        require((h, k) == ((F(11, 12), F(1)) if i < 16 else (F(12, 11), F(1))),
                "Wrong adaptive weight")
        weights.add((h, k))
        sparse = {int(j): F(value) for j, value in policy["gamma_multipliers"].items()}
        require(all(0 <= j < 32 and value >= 0 for j, value in sparse.items()),
                "Invalid Gamma multiplier")
        rho = F(policy["density_multiplier"])
        require(rho >= 0, "Negative density multiplier")
        for vi, g in enumerate(grid):
            trigger = uniform[vi][i]
            n, m, total, _, _ = quantities(g, h, k)
            require(total > 0, "Nonpositive normalizer")
            for j, margin in enumerate(gamma_margins(g, gamma_cap, h, k)):
                check("adaptive_gamma_checks", margin + sparse.get(j, F(0)) * trigger)
            density_margin = density_cap * total - max(h, k) * (n + m)
            check("adaptive_density_checks", density_margin + rho * trigger)

    r_maximum = F(0)
    for h, k in sorted(weights):
        for g in grid:
            _, _, total, _, nums = quantities(g, h, k)
            require(len(nums) == expected["r_branches"] == 16, "Wrong R branch count")
            for num in nums:
                check("fixed_weight_r_checks", r_cap * total - num)
                r_maximum = max(r_maximum, num / total)
    require(r_maximum == F(expected["fixed_weight_r_envelope_maximum"]) == r_cap,
            "Wrong fixed-weight R maximum")
    # These fallback bounds are established in the accompanying proof's sources.
    require(F(certificate["uniform_r_cap"]) == F(15, 7) <= r_cap,
            "Uniform fallback R exceeds target")
    absent = certificate["absent_modulus_three"]
    require(F(absent["gamma_cap"]) == F(215, 24) <= gamma_cap,
            "Absent-modulus Gamma exceeds target")
    require(F(absent["r_cap"]) == F(17, 12) <= r_cap,
            "Absent-modulus R exceeds target")
    require(density_cap >= 1, "Uniform fallback density exceeds target")
    for category, count in counts.items():
        require(count == expected[category], f"Wrong {category} count")
    require(sum(counts.values()) == expected["total_margin_checks"] == 13824,
            "Wrong total check count")
    g3, r3 = propagate(gamma_cap, r_cap, 7)
    g4, r4 = propagate(g3, r3, 11)
    for key, actual in (("coherent_three_prime_gamma", g3),
                        ("coherent_three_prime_r", r3),
                        ("coherent_four_prime_gamma", g4),
                        ("coherent_four_prime_r", r4)):
        require(actual == F(expected[key]), f"Incorrect propagation: {key}")
    require(g4 > F(4939031, 47730), "Unexpected four-prime comparison")
    print(json.dumps({
        "result": "PASS", "vertices": len(grid), "margin_checks": sum(counts.values()),
        "minimum_margins": {key: str(value) for key, value in minimum.items()},
        "gamma_cap": str(gamma_cap), "r_cap": str(r_cap),
        "density_cap": str(density_cap), "minimum_root_mass": str(root_minimum),
        "coherent_three_prime": {"gamma": str(g3), "r": str(r3)},
        "coherent_four_prime": {"gamma": str(g4), "r": str(r4)},
    }, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/nonuniform_coupled_certificate.json'))
    args = parser.parse_args()
    verify(json.loads(read_artifact_text(args.certificate, encoding="utf-8")))


if __name__ == "__main__":
    main()
