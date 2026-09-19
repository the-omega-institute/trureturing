#!/usr/bin/env python3
"""Verify exact constants for general head laws and block tail obstructions.

Only the standard library is used. All comparisons use integers or
fractions. The arbitrary-height block theorem and cylinder estimates
remain ordinary mathematical proofs; this is not Lean certification.
The default run reads and checks the fixed adjacent JSON certificate.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product as cartesian_product
from math import gcd, isqrt, prod
from pathlib import Path
import argparse
import json

HEAD_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
               37, 41, 43, 47, 53, 59, 61, 67, 71, 73)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def primes_to(limit):
    prime = [True] * (limit + 1)
    prime[0] = prime[1] = False
    for divisor in range(2, isqrt(limit) + 1):
        if prime[divisor]:
            for value in range(divisor * divisor, limit + 1, divisor):
                prime[value] = False
    result = [value for value in range(2, limit + 1) if prime[value]]
    trial = [value for value in range(2, limit + 1)
             if all(value % divisor for divisor in range(2, isqrt(value) + 1))]
    require(result == trial, "sieve and trial-division prime lists agree")
    return result


def ternary_profile(height):
    require(height >= 1, "positive ternary height")
    r = F(1, 3 ** height)
    density = (1 - r) / 2
    first_sum = sum((F(1, 3 ** e) for e in range(1, height + 1)), F(0))
    chi_sum = sum((F(2 * e + 1, 3 ** e) for e in range(1, height + 1)), F(0))
    require(first_sum == density, "ternary first-moment sum")
    require(chi_sum == 2 - (height + 2) * r, "finite ternary chi sum")
    chi_factor = 1 + chi_sum / density
    require(chi_factor == 5 - 2 * height * r / (1 - r) < 5,
            "finite ternary Gamma factor")
    require(1 + first_sum / density == 2, "finite ternary cylinder factor")
    return {"height": height, "density": str(density), "chi_sum": str(chi_sum),
            "chi_factor": str(chi_factor), "cylinder_factor": "2"}


def binary_path_regression():
    """Compare exact messages with all eight assignments for every 3-node CSP."""
    def phi(t):
        return t - t ** 3 / 3

    count = 0
    minimum_energy = None
    for u0, u1, u2, e1, e2 in cartesian_product(
            range(4), range(4), range(4), range(16), range(16)):
        rows2 = [u2 | ((e2 >> (2 * z)) & 3) for z in range(2)]
        b2 = sum(1 << z for z in range(2) if rows2[z] == 3)
        rows1 = [u1 | ((e1 >> (2 * z)) & 3) for z in range(2)]
        b1 = sum(1 << z for z in range(2) if rows1[z] | b2 == 3)
        saturated = (u0 | b1) == 3
        solutions = [
            (x, y, z) for x, y, z in cartesian_product(range(2), repeat=3)
            if not ((u0 >> x) & 1 or (u1 >> y) & 1 or (u2 >> z) & 1
                    or (e1 >> (2 * x + y)) & 1 or (e2 >> (2 * y + z)) & 1)]
        require(saturated == (not solutions), "messages agree with exhaustive assignments")
        energies = [F(u0.bit_count() ** 2, 4),
                    F(sum(row.bit_count() ** 2 for row in rows1), 8),
                    F(sum(row.bit_count() ** 2 for row in rows2), 8)]
        betas = [F(int(saturated)), F(b1.bit_count(), 2), F(b2.bit_count(), 2), F(0)]
        require(all(phi(betas[i]) <= energies[i] + phi(betas[i + 1])
                    for i in range(3)), "actual-message cubic potential inequality")
        energy = sum(energies, F(0))
        require(not saturated or F(3, 2) * energy >= 1, "actual saturation energy")
        if saturated:
            minimum_energy = (energy if minimum_energy is None
                              else min(minimum_energy, energy))
        count += 1
    require(count == 16384 and minimum_energy == F(3, 4),
            "complete binary-path constraint corpus")
    return {"vertices": 3, "coordinate_cardinality": 2, "cases": count,
            "minimum_unsatisfiable_energy": str(minimum_energy),
            "message_assignment_equivalence": True, "local_potential_checks": True,
            "scope": "Finite regression; the arbitrary-forest theorem is an ordinary proof."}


def unrestricted_energy_boundary():
    """A fully enumerated abstract CSP, not a distinct-modulus covering system."""
    alphabet = range(3)
    assignments = list(cartesian_product(alphabet, repeat=4))
    uncovered = [assignment for assignment in assignments
                 if not (any(value == 0 for value in assignment[:3])
                         or all(value != 0 for value in assignment[:3]))]
    last_energy = F(sum(all(value != 0 for value in row)
                        for row in cartesian_product(alphabet, repeat=3)), 3 ** 3)
    energy = 3 * F(1, 3) ** 2 + last_energy
    require(len(assignments) == 81 and not uncovered and energy == F(17, 27) < F(2, 3),
            "abstract full coverage refutes an unrestricted forest-energy threshold")
    return {"alphabet_cardinality": 3, "predecessor_count": 3,
            "assignments": len(assignments), "uncovered_assignments": len(uncovered),
            "total_square_energy": str(energy),
            "distinct_original_modulus_hypothesis": False,
            "scope": "Abstract CSP boundary; not an odd distinct covering counterexample."}


def finite_head_supported_laws():
    """Recompute finite pure-survivor caps and the unit-load conditioning gain."""
    rows = []
    for period, heights, expected_mixed, expected_square, expected_gamma in [
            (315, ((3, 2), (5, 1), (7, 1)), F(49, 120), F(399, 40), F(1148, 71)),
            (945, ((3, 3), (5, 1), (7, 1)), F(157, 336), F(189, 16), F(3812, 179))]:
        require(prod(p ** h for p, h in heights) == period, "finite head factorization")
        coordinate_rows = []
        ratios = []
        factors = []
        densities = []
        for prime, height in heights:
            u = sum((F(1, prime ** e) for e in range(1, height + 1)), F(0))
            kappa = sum((F(2 * e + 1, prime ** e) for e in range(height + 1)), F(0))
            pair_sum = sum((F(1, prime ** max(e, f))
                            for e in range(height + 1) for f in range(height + 1)), F(0))
            require(kappa == pair_sum and 0 < u < 1, "finite exponent-pair mass")
            rho = 1 - u
            ratios.append(u / rho)
            factors.append(1 + (kappa - 1) / rho)
            densities.append(rho)
            coordinate_rows.append({"prime": prime, "height": height, "u": str(u),
                                    "pure_survivor_density_lower": str(rho),
                                    "uniform_kappa": str(kappa),
                                    "survivor_pair_factor": str(factors[-1])})
        mixed = prod(1 + ratio for ratio in ratios) - 1 - sum(ratios, F(0))
        square = prod(factors)
        require(mixed == expected_mixed < 1 and square == expected_square,
                "finite-head mixed deletion and product moment")
        gamma = 1 + (square - 1) / (1 - mixed)
        require(gamma == expected_gamma < square / (1 - mixed),
                "unit-divisor lower bound improves conditioned second moment")
        survivor_count = period * prod(densities) * (1 - mixed)
        require(survivor_count == (71 if period == 315 else 179),
                "finite-head actual-survivor count lower bound")
        rows.append({"period_bound": period, "coordinates": coordinate_rows,
                     "mixed_budget": str(mixed), "product_moment_bound": str(square),
                     "Gamma_bound": str(gamma), "uncovered_count_lower": str(survivor_count)})
    return rows


def local_kernel_crt_regression():
    """Check sequential kernels against actual, distinct CRT modulus labels."""
    primes = (3, 5, 7, 11)
    tails = primes[1:]
    moduli = sorted(prod(subset) for size in range(1, 5)
                    for subset in combinations(primes, size))
    head = {1: F(1, 3), 2: F(2, 3)}
    gamma = 1 + 3 * max(head.values())
    cases = queries = assignment_count = 0
    for seed, delta in cartesian_product((1, 7, 19, 113), (F(1, 3), F(2, 5))):
        state = seed
        residue = {}
        for modulus in moduli:
            state = (1664525 * state + 1013904223) % (2 ** 32)
            residue[modulus] = state % modulus
        residue[3] = 0
        labels = {v: [d for d in moduli if any(d % p == 0 for p in tails)
                      and max(p for p in tails if d % p == 0) == v] for v in tails}
        law = {(x,): mass for x, mass in head.items()}
        earlier = []
        born = {}
        cap = 1 / (1 - delta)
        for vertex in tails:
            extended = {}
            moment = forbidden_probability = F(0)
            for history, mass in law.items():
                coords = dict(zip((3, *earlier), history))
                forbidden = {residue[d] % vertex for d in labels[vertex]
                             if all(coords[p] == residue[d] % p
                                    for p in coords if d % p == 0)}
                alpha = F(len(forbidden), vertex)
                moment += mass * alpha ** 2
                forbidden_probability += mass * max(F(0), alpha - delta) / (1 - delta)
                for value in range(vertex):
                    if alpha <= delta:
                        density = F(0) if value in forbidden else 1 / (1 - alpha)
                    else:
                        density = ((alpha - delta) / (alpha * (1 - delta))
                                   if value in forbidden else cap)
                    require(0 <= density <= cap, "pointwise capped-kernel bound")
                    extended[(*history, value)] = mass * density / vertex
            require(sum(extended.values(), F(0)) == 1, "normalized complete prefix law")
            moment_bound = gamma * F(1, vertex ** 2) * prod(1 + cap * F(3, p) for p in earlier)
            require(moment <= moment_bound, "actual-label local moment bound")
            require(forbidden_probability <= moment_bound / (4 * delta * (1 - delta)),
                    "assigned violation bound")
            born[vertex] = forbidden_probability
            law = extended
            earlier.append(vertex)
        direct = {v: F(0) for v in tails}
        union_mass = F(0)
        for history, mass in law.items():
            coords = dict(zip(primes, history))
            some = False
            for vertex in tails:
                bad = any(all(coords[p] == residue[d] % p for p in primes if d % p == 0)
                          for d in labels[vertex])
                if bad:
                    direct[vertex] += mass
                    some = True
            if some:
                union_mass += mass
            assignment_count += 1
        require(direct == born, "future kernels preserve actual violation probabilities")
        require(union_mass <= sum(direct.values(), F(0)), "actual final union bound")
        for size in range(1, 4):
            for subset in combinations(range(1, 4), size):
                marginal = {}
                for history, mass in law.items():
                    key = (history[0], *(history[i] for i in subset))
                    marginal[key] = marginal.get(key, F(0)) + mass
                bound = prod(cap / primes[i] for i in subset)
                for key, mass in marginal.items():
                    require(mass <= head[key[0]] * bound, "conditional selective-coordinate cap")
                    queries += 1
        cases += 1
    require(cases == 8 and assignment_count == 6160 and queries == 9200,
            "complete fixed actual-CRT kernel corpus")
    return {"cases": cases, "full_assignments": assignment_count,
            "conditional_cylinder_queries": queries, "period": 1155,
            "head_weights": ["1/3", "2/3"], "original_distinct_moduli": moduli,
            "scope": "Actual CRT regression; the general local-kernel theorem is an ordinary proof."}
