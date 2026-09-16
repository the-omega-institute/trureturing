#!/usr/bin/env python3
"""Exact counterexamples to two proposed odd-covering proof steps.

Python 3.8+ standard library; no network or Lean invocation. Run with
--source-archive three_prime_factors_complete.zip (see the Problems dossier).
The archive hash and source substrings bind the formulas to Michael Schroeder,
DOI 10.5281/zenodo.22760638 (code MIT, prose CC BY 4.0); they are not kernel
verification. These finite calculations do not settle Erdős problem #7.
"""

import argparse
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from io import BytesIO
from itertools import combinations, product
from math import prod
from pathlib import Path
import sys
from zipfile import BadZipFile, ZipFile


ARCHIVE_SHA256 = "5956327277ac47dd6e98a0a38f2a785cd61e647560c7f6ab5c73a63cf49faa51"


def check(condition, description):
    """Validation remains active with python -O."""
    if not condition:
        raise ValueError(description)


def bind_source(archive):
    data = archive.read_bytes()
    digest = sha256(data).hexdigest()
    check(digest == ARCHIVE_SHA256, "source archive SHA-256 mismatch: " + digest)
    snippets = {
        "formal/Erdos7/CappedGainDepth.lean": (
            "def beta (p : ℚ) (d : ℕ) : ℚ := (p - 1) / p ^ d",
        ),
        "formal/Erdos7/ThreePrime/Counts.lean": (
            "(old.1 + (old.2+1)*x (Fin.last n), old.2+x (Fin.last n))",
        ),
        "formal/Erdos7/ThreePrime/Comparison.lean": (
            "S.filter (fun c ↦ ∀ i, depth c i ≤ (x i).val)",
        ),
        "formal/Erdos7/ThreePrime/Model.lean": (
            "sparse : ∀ c ∈ labels, supportSize (depth c) ≤ 3",
        ),
        "formal/Erdos7/ThreePrime/Schedule.lean": (
            "| 3 => 0 | 5 => 0 | 7 => 1/5 | 11 => 1/3 | 13 => 6/11",
        ),
        "formal/Erdos7/Distortion.lean": (
            "if α ≤ δ then 0 else (α - δ) / (α * (1 - δ))",
            "if α ≤ δ then (1 - α)⁻¹ else (1 - δ)⁻¹",
            "if α ≤ δ then 0 else (α - δ) / (1 - δ)",
            "weight := fun ω ↦ μ.weight ω *",
        ),
        "formal/Erdos7/ThreePrime/Arithmetic.lean": (
            "theorem noncoverage_at_most_three_prime_factors",
            "(hThree : ∀ k, (modulus k).primeFactors.card ≤ 3)",
        ),
    }
    # Inspect exactly the bytes hashed above; do not extract or execute the ZIP.
    with ZipFile(BytesIO(data)) as source_zip:
        for suffix, expected in snippets.items():
            names = [name for name in source_zip.namelist() if name.endswith(suffix)]
            check(len(names) == 1, "source member is missing or ambiguous: " + suffix)
            text = source_zip.read(names[0]).decode("utf-8")
            for snippet in expected:
                check(snippet in text, "source substring mismatch: " + suffix)


def beta(p, depth):
    return Q(p - 1, p ** depth)


def threshold_mass(delta, probability):
    return Q(0) if probability <= delta else (probability - delta) / (1 - delta)


def quadratic_bridge():
    primes = (3, 5, 7, 11)
    old, terminal = primes[:-1], primes[-1]
    period = prod(primes)
    subsets = [s for size in (1, 2, 3) for s in combinations(range(3), size)]
    pure = [(0, p) for p in primes]
    mixed, depths = [], []
    for digit, subset in enumerate(subsets, 1):
        cofactor = prod(primes[j] for j in subset)
        modulus = terminal * cofactor
        residue = (1 + cofactor * (((digit - 1) * pow(cofactor, -1, terminal))
                                  % terminal)) % modulus
        mixed.append((residue, modulus))
        depths.append(tuple(int(j in subset or j == 3) for j in range(4)))
    family = pure + mixed
    check(mixed == [(1, 33), (46, 55), (36, 77), (136, 165),
                    (148, 231), (281, 385), (106, 1155)], "first CRT family")
    check(len({m for a, m in family}) == len(family), "first moduli distinct")
    check(all(m > 1 and m % 2 == 1 and period % m == 0 for a, m in family),
          "first moduli odd, nontrivial and periodic")
    check(all(p >= 3 for p in primes), "prime_three data")
    check(len(set(depths)) == len(depths), "depth injectivity")
    check([sum(d) for d in depths] == [2, 2, 2, 3, 3, 3, 4], "mixed and sparse boundary")
    check(all(d[-1] == 1 for d in depths), "all mixed classes end at 11")

    # Height one: remove digit zero at each prime, then use the uniform product.
    space = list(product(*(range(1, p) for p in primes)))
    check(len(space) == 480, "physical product space")

    def hit(c, j, y):
        return depths[c][j] == 0 or y[j] == mixed[c][0] % primes[j]

    for c, depth in enumerate(depths):
        for j, p in enumerate(primes):
            probability = Q(sum(hit(c, j, y) for y in space), len(space))
            if depth[j] == 0:
                check(probability == 1, "zero_hit data")
            else:
                check(probability == Q(1, p - 1), "nonzero digit probability")
                check(probability <= beta(p, depth[j]) / (p - 2), "base prefix_cap")
    for n in range(period):
        y = tuple(n % p for p in primes)
        for c, (a, m) in enumerate(mixed):
            check((n % m == a) == all(hit(c, j, y) for j in range(4)),
                  "first arithmetic/cylinder equivalence")

    # Earlier ending sets are empty. This is an actual positive-mass old prefix.
    x, heights = (1, 1, 1, 1), (1, 1, 1)
    active = [c for c in range(len(mixed)) if all(hit(c, j, x) for j in range(3))]
    aligned = [c for c in range(len(mixed))
               if all(depths[c][j] <= heights[j] for j in range(3))]
    check(active == aligned == list(range(7)), "seven active and aligned classes")
    prefix_mass = Q(1, prod(p - 1 for p in old))
    check(prefix_mass == Q(1, 48), "positive physical prefix mass")
    check(mixed[6][1] // terminal == 105, "cubic old cofactor")

    count, height_sum = 0, 0
    for k in heights:
        count, height_sum = count + (height_sum + 1) * k, height_sum + k
    check(count == sum(heights) + sum(heights[i] * heights[j]
                                     for i, j in combinations(range(3), 2)) == 6,
          "quadratic countState recurrence")
    full_count = prod(1 + k for k in heights) - 1
    load = sum((beta(terminal, depths[c][-1]) for c in aligned), Q(0))
    check(full_count == 7, "full cofactor count")
    check(load == Q(70, 11) and load - count == Q(4, 11) > 0, "load exceeds count")

    selected = [r for r in range(1, terminal)
                if any(hit(c, 3, (1, 1, 1, r)) for c in active)]
    check(selected == list(range(1, 8)), "seven disjoint terminal hits")
    alpha = Q(len(selected), terminal - 1)
    check(alpha == Q(7, 10) and alpha > Q(count, terminal - 2), "quadratic alpha cap fails")
    check(alpha <= load / (terminal - 2), "original union/load bound holds")

    essential = []
    for c, (a, m) in enumerate(mixed):
        witnesses = [n for n in range(period)
                     if n % prod(old) == 1 and n % terminal == c + 1]
        check(len(witnesses) == 1, "unique CRT lift")
        n = witnesses[0]
        check([i for i, (b, q) in enumerate(family) if n % q == b] == [len(pure) + c],
              "each mixed class has an exclusive coverage witness")
        essential.append(n)

    deltas = (Q(0), Q(0), Q(1, 5))
    auxiliary_mass = prod(Q(p - 1, p * (p - 2)) / (1 - d) for p, d in zip(old, deltas))
    check(auxiliary_mass == Q(4, 105), "positive auxiliary height mass")
    delta11 = Q(1, 3)
    actual_charge = threshold_mass(delta11, alpha)
    quadratic_charge = max(Q(count) - (terminal - 2) * delta11, Q(0)) / (
        (terminal - 2) * (1 - delta11))
    check(actual_charge == Q(11, 20) and quadratic_charge == Q(1, 2), "local hinge gap")

    print("Quadratic bridge family (residue, modulus):", family)
    print("Old prefix: 1 mod 105; mass:", prefix_mass, "; auxiliary mass:", auxiliary_mass)
    print("Quadratic count:", count, "; full count:", full_count, "; beta-load:", load)
    print("Bad probability:", alpha, "; quadratic cap:", Q(count, terminal - 2))
    print("Threshold mass:", actual_charge, "; quadratic substitute:", quadratic_charge)
    print("Exclusive mixed-class witnesses:", essential, "; cubic cofactor: 105")


def distort(law, bad, delta):
    probability = sum((w for x, w in law.items() if bad(x)), Q(0))
    inside = (Q(0) if probability <= delta else
              (probability - delta) / (probability * (1 - delta)))
    outside = (1 / (1 - probability) if probability <= delta else 1 / (1 - delta))
    result = {x: w * (inside if bad(x) else outside) for x, w in law.items()}
    check(sum(result.values(), Q(0)) == 1, "distorted law normalized")
    return result


def survivor_conditioning_bridge():
    history = [(1, 3), (1, 5), (1, 7), (2, 15)]
    pure = [(10, 11)]
    mixed = [(0, 33), (45, 55), (35, 77), (135, 165),
             (147, 231), (280, 385), (105, 1155)]
    family = history + pure + mixed
    check(len(family) == len({m for a, m in family}) == 12, "second moduli distinct")
    check(all(m > 1 and m % 2 == 1 and 1155 % m == 0 for a, m in family),
          "second moduli odd, nontrivial and periodic")
    pure_survivors = [x for x in range(105) if all(x % p != 1 for p in (3, 5, 7))]
    survivors = [x for x in pure_survivors if x % 15 != 2]
    check(len(pure_survivors) == 48 and len(survivors) == 42 and 0 in survivors,
          "pure and complete history survivor counts")
    mu = {x: Q(1, 48) for x in pure_survivors}
    nu = {x: Q(1, 42) if x in survivors else Q(0) for x in pure_survivors}

    # Scalar-coordinate marginal of the source's physical prefix law. The other
    # coordinates of CylinderModel.Space are independent dummy coordinates.
    base3 = {r: Q(1, 2) for r in range(3) if r != 1}
    base5 = {r: Q(1, 4) for r in range(5) if r != 1}
    base7 = {r: Q(1, 6) for r in range(7) if r != 1}
    kernel3 = distort(base3, lambda r: False, Q(0))
    kernel5 = {r3: distort(base5, lambda r5: r3 == 2 and r5 == 2, Q(0)) for r3 in base3}
    kernel7 = distort(base7, lambda r: False, Q(1, 5))
    check(kernel3 == base3 and kernel7 == base7, "empty-event kernels")
    check(all(kernel == base5 for kernel in kernel5.values()), "delta5 zero preserves law")
    physical = {x: kernel3[x % 3] * kernel5[x % 3][x % 5] * kernel7[x % 7]
                for x in pure_survivors}
    check(physical == mu and mu != nu, "physical law differs from conditioned law")
    check(sum((w for x, w in mu.items() if x % 15 == 2), Q(0)) == Q(1, 8),
          "earlier mixed event retains positive physical mass")

    for n in range(1155):
        for c, (a, m) in enumerate(mixed):
            cofactor = m // 11
            check(a % cofactor == 0 and a % 11 == c, "second CRT residues")
            check((n % m == a) == (n % cofactor == 0 and n % 11 == c),
                  "second arithmetic/cylinder equivalence")

    # Count actual integer lifts, independently of the cofactor formula.
    charges, support_counts = {}, {}
    for x in pure_survivors:
        lifts = [n for n in range(x, 1155, 105) if n % 11 != 10]
        check(len(lifts) == 10, "terminal lifts avoid current pure class")
        hit_lifts = [n for n in lifts if any(n % m == a for a, m in mixed)]
        check(all(sum(n % m == a for a, m in mixed) <= 1 for n in lifts),
              "second terminal hits disjoint")
        alpha = Q(len(hit_lifts), len(lifts))
        support_counts[x] = sum(x % p == 0 for p in (3, 5, 7))
        check(alpha == Q(2 ** support_counts[x] - 1, 10), "actual lifts match full count")
        charges[x] = threshold_mass(Q(1, 3), alpha)
    check({x: v for x, v in charges.items() if v > 0} == {0: Q(11, 20)},
          "only zero prefix has positive charge")
    e_mu = sum((mu[x] * charges[x] for x in pure_survivors), Q(0))
    e_nu = sum((nu[x] * charges[x] for x in pure_survivors), Q(0))
    check(e_mu == Q(11, 960) and e_nu == Q(11, 840), "conditioning increases charge")
    check(e_nu / e_mu == Q(8, 7), "charge normalization ratio")
    condition = [x for x in survivors if x % 3 == 2]
    conditional_probability = Q(sum(x % 5 == 0 for x in condition), len(condition))
    check(len(condition) == 18 and conditional_probability == Q(1, 3) > Q(4, 15),
          "conditioning violates old prefix cap")

    counts = Counter(support_counts[x] for x in survivors)
    check(tuple(counts[s] for s in range(4)) == (10, 22, 9, 1), "survivor support counts")
    quadratic_expectation = sum((
        nu[x] * max(Q(support_counts[x] * (support_counts[x] + 1), 2) - 3, Q(0)) / 6
        for x in pure_survivors), Q(0))
    check(quadratic_expectation == Q(1, 84) < e_nu, "conditioned quadratic expectation fails")
    uncovered = [n for n in range(1155) if all(n % m != a for a, m in family)]
    check(len(uncovered) == 364 and 3 in uncovered, "second family does not cover")
    check(Q(len(uncovered), 1155) == Q(52, 165), "uncovered density in full period")

    print("Survivor-conditioning family (residue, modulus):", family)
    print("Old pure survivors:", len(pure_survivors), "; complete survivors:", len(survivors))
    print("Physical expected charge:", e_mu, "; conditioned charge:", e_nu, "; ratio:", e_nu / e_mu)
    print("nu(r5=0 | r3=2):", conditional_probability, "; old cap:", Q(4, 15))
    print("Survivor support counts:", tuple(counts[s] for s in range(4)))
    print("Conditioned quadratic expectation:", quadratic_expectation)
    print("Uncovered residues:", len(uncovered), "/ 1155; witness: 3")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-archive", required=True, type=Path,
                        help="the exact ThreePrimeDivisors ZIP identified in the dossier")
    args = parser.parse_args()
    try:
        check(sys.version_info >= (3, 8), "Python 3.8 or later is required")
        bind_source(args.source_archive)
        print("Source archive SHA-256:", ARCHIVE_SHA256)
        print("Source substring checks bind evidence only; no Lean kernel replay.")
        quadratic_bridge()
        survivor_conditioning_bridge()
    except (OSError, ValueError, BadZipFile) as error:
        print("FAIL:", error, file=sys.stderr)
        return 1
    print("PASS: both proposed proof steps fail; unrestricted Erdős #7 remains open.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
