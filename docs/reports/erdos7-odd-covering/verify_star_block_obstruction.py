#!/usr/bin/env python3
"""Verify exact constants for general head laws and block tail obstructions.

Only the standard library is used. All comparisons use integers or
fractions. The arbitrary-height block theorem and cylinder estimates
remain ordinary mathematical proofs; this is not Lean certification.
The default run reads and checks the fixed adjacent JSON certificate.
"""
from fractions import Fraction as F
from itertools import combinations, product as cartesian_product
from math import isqrt, prod
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


def support_rank_primes(limit):
    require(limit >= 2, "sieve limit must be at least two")
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b"\x00" * ((limit - p*p)//p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def pair_support_components(primes, q0, denominator=10 ** 12):
    """Upper bounds for sum a_v², sum a_v²(3A_v+2S_v), sum a_v²R_v.

    Each a_p=1/(p-1) is rounded upward individually. The third
    polynomial is represented as R=2 sum_(p<q) a_p a_q, so every
    coefficient used by the upward rounding is nonnegative.
    """
    A = S = R = T0 = T1 = T2 = count = 0
    for p in primes:
        if p < q0:
            continue
        a = (denominator + p - 2)//(p - 1)
        require(a*(p - 1) >= denominator, "reciprocal ceiling failed")
        a2 = a*a
        T0 += a2
        T1 += a2*(3*denominator*A + 2*S)
        T2 += a2*R
        R += 2*A*a
        A += a
        S += a2
        count += 1
    require(R == A*A - S, "ordered distinct-parent sum mismatch")
    return {
        "count": count,
        "T0": F(T0, denominator**2),
        "T1": F(T1, denominator**4),
        "T2": F(T2, denominator**4),
        "A0": F(A, denominator),
        "S0": F(S, denominator**2),
    }


def pair_support_bound(components, delta, G, cutoff=2 ** 20):
    require(0 < delta <= F(1, 2), "threshold outside capped-kernel range")
    require(G > 0 and cutoff > 0, "positive head bound and cutoff required")
    K = 1/(1 - delta)
    A, S = components["A0"], components["S0"]
    finite = components["T0"] + K*components["T1"] + K*K*components["T2"]
    tail = (2 + K*(6*A + 12 + 4*S + F(8, cutoff))
            + K*K*(2*A*A + 8*A + 12))/cutoff
    return {
        "K": K,
        "finite_moment_sum_upper": finite,
        "infinite_moment_tail_upper": tail,
        "loss_upper": G*(finite + tail)/(4*delta*(1 - delta)),
    }


def rank_two_tail_bounds():
    limit = 2 ** 20
    scale = 10 ** 12
    primes = support_rank_primes(limit)
    require(len(primes) == 82025, "rank-two prime count through 2^20")
    rows = []
    for head, cutoff, gamma, delta, target, expected in [
            ("complete_star_head", 79, F(177), F(2, 5), F(861, 1000),
             F(82616302964943401201866424605892182335718551607,
               96000000000000000000000000000000000000000000000)),
            ("arbitrary_357_head", 23, F(1889, 48), F(3, 8), F(947, 1000),
             F(6656641538266277932795352817051944900003690098417,
               7031250000000000000000000000000000000000000000000))]:
        components = pair_support_components(primes, cutoff, scale)
        result = pair_support_bound(components, delta, gamma, limit)
        require(result["loss_upper"] == expected < target < 1,
                "exact rank-two loss and strict threshold")
        rows.append({"head": head, "tail_prime_minimum": cutoff,
                     "Gamma_bound": str(gamma), "delta": str(delta),
                     "components": {key: str(value) if isinstance(value, F) else value
                                    for key, value in components.items()},
                     **{key: str(value) for key, value in result.items()},
                     "strict_target": str(target)})
    return {"prime_cutoff": limit, "rounding_scale": scale,
            "maximum_tail_support_per_original_modulus": 2,
            "sieve_prime_count": len(primes), "rows": rows,
            "scope": "Exact arithmetic for bounded original tail support; no graph restriction."}


def rank_three_tail_bounds():
    """Positive coefficient enumeration and an exact all-integer infinite tail."""
    limit = 2 ** 20
    scale = 10 ** 12
    primes = support_rank_primes(limit)
    require(len(primes) == 82025, "rank-three sieve count through 2^20")

    def ceiling(numerator, denominator):
        require(denominator > 0, "positive rounding denominator")
        return (numerator + denominator - 1) // denominator

    def poly_add(*terms):
        result = [F(0)] * max(map(len, terms))
        for term in terms:
            for degree, value in enumerate(term):
                result[degree] += value
        return result

    def poly_mul(left, right):
        result = [F(0)] * (len(left) + len(right) - 1)
        for i, x in enumerate(left):
            for j, y in enumerate(right):
                result[i + j] += x * y
        return result

    def poly_scale(term, value):
        return [value * x for x in term]

    # These moments solve M_k - sum_{j<=k} binom(k,j) M_j/2 = [k=0].
    # Verify via the shift identity instead of trusting a decimal tail estimate.
    from math import comb
    moments = [F(2), F(2), F(6), F(26), F(150)]
    for k, moment in enumerate(moments):
        shifted = sum((F(comb(k, j), 2) * moments[j] for j in range(k + 1)), F(0))
        require(moment - shifted == int(k == 0), "geometric power-sum identity")

    # Independent finite exponent-tuple expansion detects a support-count error.
    regression_count = 0
    for support_limit in (1, 2):
        small_primes = (3, 5, 7)
        cap = F(5, 3)
        coefficients = [[F(0)] * (support_limit + 1) for _ in range(support_limit + 1)]
        coefficients[0][0] = 1
        for prime in small_primes:
            a = sum((F(1, prime ** e) for e in (1, 2)), F(0))
            b = sum((F(1, prime ** max(e, f)) for e in (1, 2) for f in (1, 2)), F(0))
            old = coefficients
            coefficients = [row[:] for row in old]
            for i in range(support_limit + 1):
                for j in range(support_limit + 1):
                    coefficients[i][j] += cap * (
                        (a * old[i - 1][j] if i else 0)
                        + (a * old[i][j - 1] if j else 0)
                        + (b * old[i - 1][j - 1] if i and j else 0))
        tuples = [t for t in cartesian_product(range(3), repeat=3)
                  if sum(e > 0 for e in t) <= support_limit]
        direct = sum((prod(cap / p ** max(e, f) if max(e, f) else 1
                           for p, e, f in zip(small_primes, left, right))
                      for left in tuples for right in tuples), F(0))
        require(direct == sum(map(sum, coefficients)), "support polynomial matches actual exponent pairs")
        regression_count += len(tuples) ** 2

    rows = []
    for head, cutoff, gamma, delta, target in [
            ("head_divides_315", 17, F(1148, 71), F(3, 10), F(981, 1000)),
            ("head_divides_945", 19, F(3812, 179), F(7, 20), F(989, 1000))]:
        cap = 1 / (1 - delta)
        coefficients = [[0] * 3 for _ in range(3)]
        coefficients[0][0] = scale
        total = a_sum = b_sum = count = 0
        for prime in primes:
            if prime < cutoff:
                continue
            denominator = prime - 1
            a = ceiling(scale, denominator)
            b = ceiling(scale * (denominator + 2), denominator ** 2)
            square = ceiling(scale, denominator ** 2)
            total += ceiling(square * sum(map(sum, coefficients)), scale)
            old = coefficients
            coefficients = [row[:] for row in old]
            for i in range(3):
                for j in range(3):
                    increment = ((a * old[i - 1][j] if i else 0)
                                 + (a * old[i][j - 1] if j else 0)
                                 + (b * old[i - 1][j - 1] if i and j else 0))
                    coefficients[i][j] += ceiling(cap.numerator * increment,
                                                  cap.denominator * scale)
            a_sum += a
            b_sum += b
            count += 1
        # On (N 2^j, N 2^(j+1)], sum a_v^2 <= 1/(N 2^j).
        # The prefix sums increase by at most j+1 and j+1+2/(N-1).
        a_poly = [cap * (F(a_sum, scale) + 1), cap]
        b_poly = [cap * (F(b_sum, scale) + 1 + F(2, limit - 1)), cap]
        base = poly_add([1], a_poly, poly_scale(poly_mul(a_poly, a_poly), F(1, 2)))
        short = poly_add([1], a_poly)
        tail_poly = poly_add(poly_mul(base, base),
                             poly_mul(b_poly, poly_mul(short, short)),
                             poly_scale(poly_mul(b_poly, b_poly), F(1, 2)))
        tail = sum((coefficient * moment for coefficient, moment in zip(tail_poly, moments)), F(0)) / limit
        finite = F(total, scale)
        loss = gamma * (finite + tail) / (4 * delta * (1 - delta))
        require(loss < target < 1, "rank-three infinite-prime loss below one")
        rows.append({"head": head, "tail_prime_minimum": cutoff,
                     "maximum_tail_support_per_original_modulus": 3,
                     "Gamma_bound": str(gamma), "delta": str(delta),
                     "prime_count": count, "prefix_a_upper": str(F(a_sum, scale)),
                     "prefix_b_upper": str(F(b_sum, scale)),
                     "final_scaled_coefficient_matrix": coefficients,
                     "finite_sum_upper": str(finite), "dyadic_tail_polynomial": list(map(str, tail_poly)),
                     "infinite_tail_upper": str(tail), "loss_upper": str(loss),
                     "strict_target": str(target)})
    return {"prime_cutoff": limit, "rounding_scale": scale,
            "sieve_prime_count": len(primes), "geometric_power_sums": list(map(str, moments)),
            "finite_exponent_pair_regressions": regression_count, "rows": rows,
            "scope": "Exact certificate for the ordinary bounded-tail-support theorem; no graph restriction."}


def certificate():
    all_primes = primes_to(4000)
    require(tuple(p for p in all_primes if 3 <= p <= 73) == HEAD_PRIMES,
            "all 20 odd head primes")
    external_chi_factor = prod(F(p * p - p + 2, (p - 3) * (p - 1))
                               for p in HEAD_PRIMES[1:])
    external_cylinder_factor = prod(F(p - 2, p - 3) for p in HEAD_PRIMES[1:])
    k_zero = 5 * external_chi_factor
    c_zero = 2 * external_cylinder_factor
    require(F(176921, 1000) < k_zero < F(176922, 1000) < 177,
            "all-positive-height star Gamma bound")
    require(c_zero < F(73, 10), "all-positive-height star cylinder sum")
    # For S_H=2-(H+2)3^-H, S_0=0. Multiplying S_H-S_(H-1) by 3^H
    # gives -(H+2)+3(H+1)=2H+1. These are coefficients of 1 and H.
    recurrence_coefficients = [-2 + 3, -1 + 3]
    require(2 - (0 + 2) == 0 and recurrence_coefficients == [1, 2],
            "finite chi-sum base case and recurrence polynomial")
    profiles = [ternary_profile(height) for height in (1, 2, 3, 8, 31, 64)]
    selected = [prime for prime in all_primes if prime > 73]
    scale = 10 ** 9
    ceiling_sum = sum((scale + (q - 1) ** 2 - 1) // ((q - 1) ** 2)
                      for q in selected)
    exact_partial = sum((F(1, (q - 1) ** 2) for q in selected), F(0))
    require(len(selected) == 529 and ceiling_sum == 2363054,
            "fixed finite prime-square calculation")
    require(exact_partial <= F(ceiling_sum, scale), "rounded prime upper sum")
    # For q>4000 prime, q=2j+1 with j>=2000. The decreasing-function bound
    # sum_(j>=n) j^-2 <= n^-2 + integral_n^infty x^-2 dx controls the tail.
    tail_index = 2000
    odd_tail = F(1, 4 * tail_index ** 2) + F(1, 4 * tail_index)
    prime_square_upper = F(ceiling_sum, scale) + odd_tail
    require(prime_square_upper == F(4976233, 2000000000) < F(1, 400),
            "infinite prime-square upper bound")
    pair_factor = 2 * F(157, 156) ** 2
    matching_loss = F(177, 400) * pair_factor
    retained = 1 - matching_loss
    require(matching_loss == F(1454291, 1622400) < F(9, 10), "matching loss")
    require(retained == F(168109, 1622400) > F(1, 10), "matching retained fibres")
    delta = F(3, 4)
    singleton_loss = F(177, 400) / delta ** 2
    residual_threshold = 1 - singleton_loss
    pair_raw_threshold = residual_threshold * (1 - delta) ** 2
    edge_threshold = pair_raw_threshold / F(73, 10)
    require(singleton_loss == F(59, 75), "singleton loss")
    require(residual_threshold == F(16, 75), "residual crossing budget")
    require(pair_raw_threshold == F(1, 75), "two-prime raw crossing budget")
    require(edge_threshold == F(2, 1095), "weighted graph-edge threshold")
    dense_primes = [q for q in all_primes if 79 <= q <= 181]
    dense_sum = sum((F(1, q * r) for j, q in enumerate(dense_primes)
                     for r in dense_primes[j + 1:]), F(0))
    require(len(dense_primes) == 21, "dense comparison prime count")
    require(dense_sum > F(14, 1000) > F(1, 75), "simplified budget is not universal")
    # The comparison has only 0 mod qr classes and no singleton-tail classes.
    # Thus E=0 and J=16*dense_sum. It violates the simplified uniform budget
    # I<=1/75 but DOES satisfy the full E+J<1 criterion.
    dense_actual_budget = 16 * dense_sum
    require(dense_actual_budget < 1, "dense comparison satisfies full block criterion")
    # General {3,5,7} actual head: the same uniform law supplies both
    # constants. The block identities and graph reductions are proved in
    # the accompanying problem dossier; this section checks their numbers.
    general_gamma = F(1889, 48)
    general_cylinder = F(2009, 360)
    finite_31 = sum((F(1, (q - 1) ** 2) for q in HEAD_PRIMES if q >= 31), F(0))
    finite_37 = sum((F(1, (q - 1) ** 2) for q in HEAD_PRIMES if q >= 37), F(0))
    square_31_upper = prime_square_upper + finite_31
    square_37_upper = prime_square_upper + finite_37
    component_factor = 3 * F(2791, 2700) ** 2
    component_loss = general_gamma * component_factor * square_31_upper
    degree_delta = F(2, 3)
    degree_coefficient = (general_gamma / degree_delta ** 2
                          + general_cylinder * (1 / (1 - degree_delta) ** 2
                                                + F(1, 108) / (1 - degree_delta) ** 3))
    require(degree_coefficient == F(403681, 2880), "maximum-degree-two coefficient")
    degree_loss = degree_coefficient * square_37_upper
    require(component_loss == F(8083223933051729599312138630673,
                                8423301546359219520000000000000) < 1,
            "prime-31 components of size at most three")
    require(degree_loss == F(189362442782277858843265057,
                             207982754231091840000000000) < 1,
            "prime-37 maximum degree two")
    # Every rounded term exceeds its true scaled value by less than one.
    # The resulting finite prime lower bound already makes the best common
    # delta scalar expression exceed one, even before its triangle term.
    square_31_lower = F(ceiling_sum - len(selected), scale) + finite_31
    require(exact_partial > F(ceiling_sum - len(selected), scale),
            "strict rounded prime lower bound")
    gamma_cube_margin = general_gamma * square_31_lower - F(33, 50) ** 3
    cylinder_cube_margin = general_cylinder * square_31_lower - F(17, 50) ** 3
    require(gamma_cube_margin > 0 and cylinder_cube_margin > 0,
            "prime-31 common-delta scalar obstruction")
    # A sharper, separately retained prime bound supports the new graph
    # criteria. The earlier 4000 certificate and its constants stay intact.
    extended_primes = primes_to(40000)
    extended_tail = [p for p in extended_primes if p > 73]
    extended_scale = 10 ** 12
    extended_ceiling = sum((extended_scale + (p - 1) ** 2 - 1) // ((p - 1) ** 2)
                           for p in extended_tail)
    extended_odd_tail = F(1, 1600000000) + F(1, 80000)
    extended_square = F(extended_ceiling, extended_scale) + extended_odd_tail
    require(len(extended_tail) == 4182 and extended_ceiling == 2387697612,
            "extended finite prime-square sum")
    require(extended_square == F(2400198237, 10 ** 12),
            "extended infinite prime-square bound")

    def square_upper(cutoff):
        return extended_square + sum((F(1, (p - 1) ** 2)
                                      for p in HEAD_PRIMES if cutoff <= p <= 73), F(0))

    def graph_bounds(cutoff, gamma, cylinder, hub_count, matching_hubs):
        a0 = F(1, cutoff - 1)
        square = square_upper(cutoff)
        hub_primes = [p for p in extended_primes if p >= cutoff][:hub_count]
        weights = [F(1, p - 1) for p in hub_primes]
        product = prod(1 + a for a in weights)
        moment_factor = prod(1 + 3 * a + 2 * a * a for a in weights)
        cube_margin = square - hub_count * a0 * a0
        derivative_margin = (cylinder - 2 * gamma * a0 * (1 + a0)
                             * (1 + 2 * a0) ** hub_count)
        require(cube_margin >= 0 and derivative_margin > 0,
                "hub comparison is monotone on the entire padded cube")
        loss = (cylinder * (product - 1)
                + gamma * moment_factor * (square - sum(a * a for a in weights)))
        require(loss < 1, "vertex-cover exclusion")
        matching_weights = weights[:matching_hubs]
        pair_factor = 2 * (1 + a0 / 2) ** 2
        matching = (cylinder * (prod(1 + a for a in matching_weights) - 1)
                    + gamma * prod(1 + 3 * a + 2 * a * a for a in matching_weights)
                    * pair_factor * square)
        require(matching < 1, "hub deletion leaving a matching")
        return {"tail_prime_minimum": cutoff, "Gamma_bound": str(gamma),
                "cylinder_sum_bound": str(cylinder), "prime_square_upper": str(square),
                "vertex_cover_cardinality": hub_count, "worst_hub_primes": hub_primes,
                "cube_nonnegative_remainder_margin": str(cube_margin),
                "partial_derivative_lower_margin": str(derivative_margin),
                "hub_cylinder_product": str(product), "hub_moment_factor": str(moment_factor),
                "vertex_cover_loss_upper": str(loss),
                "vertex_cover_retained_lower": str(1 - loss),
                "matching_deletion_cardinality": matching_hubs,
                "matching_pair_factor": str(pair_factor), "matching_loss_upper": str(matching),
                "matching_retained_lower": str(1 - matching)}

    star_hubs = graph_bounds(79, F(177), F(73, 10), 8, 1)
    general_hubs = graph_bounds(37, general_gamma, general_cylinder, 6, 2)
    forest_rows = []
    for name, cutoff, gamma, target in [
            ("star_head", 79, F(177), F(58842, 100000)),
            ("arbitrary_357_head", 19, general_gamma, F(858311, 1000000))]:
        a0 = F(1, cutoff - 1)
        factor = 1 + 3 * a0 + 2 * a0 * a0
        loss = F(4, 3) * gamma * factor * square_upper(cutoff)
        require(loss < target < 1, "star-forest exclusion")
        forest_rows.append({"head": name, "tail_prime_minimum": cutoff,
                            "Gamma_bound": str(gamma), "maximum_center_factor": str(factor),
                            "prime_square_upper": str(square_upper(cutoff)),
                            "loss_upper": str(loss), "retained_lower": str(1 - loss)})
    # For a saturated star, alpha+sum beta>=1. The identity
    # alpha^2+1-alpha = (alpha-1/2)^2+3/4 supplies the 4/3 factor.
    require([F(1, 4) + F(3, 4), F(-1), F(1)] == [F(1), F(-1), F(1)],
            "saturation quadratic identity coefficients")
    # Exact polynomial arithmetic for the potential identity, with variables
    # b,c and Phi(t)=t-t^3/3. This checks the identity for all real b,c;
    # its sign conditions and the finite-tree cancellation are ordinary proofs.
    def polynomial_sum(*terms):
        result = {}
        for term in terms:
            for exponent, coefficient in term.items():
                result[exponent] = result.get(exponent, F(0)) + coefficient
        return {exponent: coefficient for exponent, coefficient in result.items()
                if coefficient}

    def polynomial_scale(coefficient, term):
        return {exponent: coefficient * value for exponent, value in term.items()
                if coefficient * value}

    def polynomial_product(*terms):
        result = {(0, 0): F(1)}
        for term in terms:
            products = [
                {(left[0] + right[0], left[1] + right[1]): x * y}
                for left, x in result.items() for right, y in term.items()]
            result = polynomial_sum(*products)
        return result

    one, b, c = ({(0, 0): F(1)}, {(1, 0): F(1)}, {(0, 1): F(1)})
    b_square = polynomial_product(b, b)
    c_square = polynomial_product(c, c)
    b_cube = polynomial_product(b_square, b)
    c_cube = polynomial_product(c_square, c)
    one_minus_c = polynomial_sum(one, polynomial_scale(-1, c))
    one_minus_b = polynomial_sum(one, polynomial_scale(-1, b))
    b_minus_c = polynomial_sum(b, polynomial_scale(-1, c))
    phi_b = polynomial_sum(b, polynomial_scale(F(-1, 3), b_cube))
    phi_c = polynomial_sum(c, polynomial_scale(F(-1, 3), c_cube))
    potential_left = polynomial_sum(polynomial_product(b, one_minus_c, one_minus_c),
                                    phi_c, polynomial_scale(-1, phi_b))
    potential_right = polynomial_sum(
        polynomial_product(c, one_minus_b, one_minus_b),
        polynomial_scale(F(1, 3), polynomial_product(b_minus_c, b_minus_c, b_minus_c)))
    require(potential_left == potential_right,
            "forest potential identity holds coefficient by coefficient")
    arbitrary_forest_rows = []
    for name, cutoff, gamma, target, expected_loss in [
            ("arbitrary_357_head", 19, general_gamma, F(965600, 1000000),
             F(6024840902671133365942778501, 6239482626932755200000000000)),
            ("star_head", 79, F(177), F(661972, 1000000),
             F(11187323982657, 16900000000000))]:
        a0 = F(1, cutoff - 1)
        factor = 1 + 3 * a0 + 2 * a0 * a0
        loss = F(3, 2) * gamma * factor * square_upper(cutoff)
        require(loss == expected_loss < target < 1, "arbitrary-forest exclusion")
        finite_profiles = []
        for height in (1, 2, 8):
            exponent_pairs = sum((F(1, cutoff ** max(e, f))
                                  for e in range(height + 1)
                                  for f in range(height + 1)), F(0))
            counted_pairs = 1 + sum((F(2 * e + 1, cutoff ** e)
                                      for e in range(1, height + 1)), F(0))
            require(exponent_pairs == counted_pairs < factor,
                    "finite parent coefficient retains pure and edge labels")
            finite_profiles.append({"height": height, "coefficient": str(counted_pairs)})
        arbitrary_forest_rows.append({
            "head": name, "tail_prime_minimum": cutoff, "Gamma_bound": str(gamma),
            "maximum_parent_factor": str(factor), "saturation_energy_factor": "3/2",
            "prime_square_upper": str(square_upper(cutoff)),
            "loss_upper": str(loss), "retained_lower": str(1 - loss),
            "finite_parent_coefficients": finite_profiles})
    feedback_rows = []
    for name, cutoff, gamma, depth, target, expected_loss in [
            ("arbitrary_357_head", 23, general_gamma, 1, F(956460, 1000000),
             F(1175604260732733206684398339119, 1229120627265994463000000000000)),
            ("star_head", 79, F(177), 2, F(966288, 1000000),
             F(16950596065609491264623331474432, 17541985668975977644799361621325))]:
        a0 = F(1, cutoff - 1)
        parent_factor = 1 + 3 * a0 + 2 * a0 * a0
        coefficient = F(3, 2) * parent_factor
        levels = [{"feedback_vertices": 0, "coefficient": str(coefficient)}]
        for level in range(1, depth + 1):
            previous = coefficient
            z = previous * parent_factor
            require(z >= F(3, 2) and 4 * z - 1 > 0, "feedback recurrence denominator")
            linear = 4 * z / (4 * z - 1)
            coefficient = 4 * z * z / (4 * z - 1)
            require(linear > 1 and coefficient == linear * z
                    and linear - linear * linear / (4 * coefficient) == 1,
                    "feedback root quadratic has exact minimum one")
            require(coefficient >= z >= previous,
                    "feedback recurrence dominates all smaller feedback sets")
            levels.append({"feedback_vertices": level, "coefficient": str(coefficient),
                           "linear_coefficient": str(linear), "z": str(z)})
        loss = gamma * coefficient * square_upper(cutoff)
        require(loss == expected_loss < target < 1, "bounded feedback-vertex exclusion")
        feedback_rows.append({
            "head": name, "tail_prime_minimum": cutoff, "Gamma_bound": str(gamma),
            "maximum_parent_factor": str(parent_factor),
            "feedback_vertices_per_component": depth, "levels": levels,
            "prime_square_upper": str(square_upper(cutoff)),
            "loss_upper": str(loss), "retained_lower": str(1 - loss)})
    finite_heads = finite_head_supported_laws()
    finite_gamma = {row["period_bound"]: F(row["Gamma_bound"]) for row in finite_heads}
    degeneracy_rows = []
    for name, cutoff, gamma, degree, threshold, target in [
            ("arbitrary_357_forest", 17, general_gamma, 1, F(11, 25), F(955226, 1000000)),
            ("arbitrary_357_degree2", 19, general_gamma, 2, F(41, 100), F(885762, 1000000)),
            ("arbitrary_357_planar", 23, general_gamma, 5, F(37, 100), F(945592, 1000000)),
            ("star_head_degree20", 79, F(177), 20, F(9, 25), F(990060, 1000000)),
            ("finite_315_head_planar", 17, finite_gamma[315], 5, F(7, 20), F(808363, 1000000)),
            ("finite_945_head_planar", 19, finite_gamma[945], 5, F(9, 25), F(732710, 1000000))]:
        require(0 < threshold <= F(1, 2), "capped-kernel threshold range")
        primes = [p for p in extended_primes if p >= cutoff][:degree + 1]
        require(len(primes) == degree + 1, "complete distinct-parent prefix")
        weights = [F(1, p - 1) for p in primes]
        factors = [1 + (3 * a + 2 * a * a) / (1 - threshold) for a in weights]
        require(all(factors[i] > factors[i + 1] > 1 for i in range(degree)),
                "parent factors strictly decrease along allowed primes")
        parent_product = prod(factors[:-1])
        square = square_upper(cutoff)
        first_squares = sum((a * a for a in weights[:-1]), F(0))
        correction = sum((a * a * (factors[-1] / factor - 1)
                          for a, factor in zip(weights[:-1], factors[:-1])), F(0))
        adjusted_square = square + correction
        positive_decomposition = (square - first_squares
                                  + sum((a * a * factors[-1] / factor
                                         for a, factor in zip(weights[:-1], factors[:-1])), F(0)))
        require(square > first_squares and correction < 0
                and adjusted_square == positive_decomposition > 0,
                "self-parent exclusion retains a positive completed vertex sum")
        denominator = 4 * threshold * (1 - threshold)
        loss = gamma * parent_product * adjusted_square / denominator
        uniform_loss = gamma * square * factors[0] ** degree / denominator
        require(loss < uniform_loss and loss < target < 1,
                "local-parent capped-kernel noncoverage criterion")
        degeneracy_rows.append({
            "head_and_graph": name, "tail_prime_minimum": cutoff,
            "Gamma_bound": str(gamma), "degeneracy": degree,
            "delta": str(threshold), "kernel_density_cap": str(1 / (1 - threshold)),
            "violation_denominator": str(denominator), "comparison_primes": primes,
            "parent_factors": [str(factor) for factor in factors],
            "distinct_parent_product": str(parent_product),
            "prime_square_upper": str(square), "self_parent_correction": str(correction),
            "adjusted_square_sum": str(adjusted_square),
            "uniform_parent_loss_upper": str(uniform_loss),
            "loss_upper": str(loss), "retained_lower": str(1 - loss)})
    leaf_moment_coefficient = general_gamma * (1 + 3 * (F(3, 36) + F(2, 36 ** 2)))
    require(leaf_moment_coefficient == F(511919, 10368) < degree_coefficient,
            "pendant-leaf coefficient is dominated by the degree-two core coefficient")
    pendant_loss = degree_coefficient * square_upper(37)
    require(pendant_loss < F(898149, 1000000) < 1, "pendant degree-two core exclusion")
    pendant_core = {"tail_prime_minimum": 37, "core_threshold": "2/3",
                    "core_coefficient": str(degree_coefficient),
                    "leaf_coefficient": str(leaf_moment_coefficient),
                    "prime_square_upper": str(square_upper(37)),
                    "loss_upper": str(pendant_loss), "retained_lower": str(1 - pendant_loss)}
    general_head = {
        "primes": [3, 5, 7], "same_uniform_law_Gamma_bound": str(general_gamma),
        "same_uniform_law_complete_cylinder_sum_bound": str(general_cylinder),
        "tail_prime_square_31_upper": str(square_31_upper),
        "tail_prime_square_37_upper": str(square_37_upper),
        "component_at_most_three_prime_31_factor": str(component_factor),
        "component_at_most_three_prime_31_loss_upper": str(component_loss),
        "component_at_most_three_prime_31_retained_lower": str(1 - component_loss),
        "maximum_degree_two_prime_37_delta": str(degree_delta),
        "maximum_degree_two_prime_37_coefficient": str(degree_coefficient),
        "maximum_degree_two_prime_37_loss_upper": str(degree_loss),
        "maximum_degree_two_prime_37_retained_lower": str(1 - degree_loss),
        "prime_31_common_delta_scalar_boundary": {
            "finite_prime_square_lower": str(square_31_lower),
            "Gamma_times_lower_exceeds_33_over_50_cubed": True,
            "cylinder_times_lower_exceeds_17_over_50_cubed": True,
            "Gamma_cube_margin": str(gamma_cube_margin),
            "cylinder_cube_margin": str(cylinder_cube_margin),
            "scope": "Only the common-delta scalar sufficient expression; not a covering counterexample."}}
    return {
        "general_357_head": general_head,
        "extended_prime_square": {"cutoff": 40000, "scale": extended_scale,
                                  "prime_count": len(extended_tail), "ceiling_sum": extended_ceiling,
                                  "odd_integer_tail": str(extended_odd_tail),
                                  "upper_bound": str(extended_square)},
        "star_forest": forest_rows, "pendant_degree_two_core": pendant_core,
        "arbitrary_forest": arbitrary_forest_rows,
        "feedback_vertex": feedback_rows,
        "finite_head_supported_laws": finite_heads,
        "local_parent_capped_kernel": degeneracy_rows,
        "rank_two_tail": rank_two_tail_bounds(),
        "rank_three_tail": rank_three_tail_bounds(),
        "local_kernel_crt_regression": local_kernel_crt_regression(),
        "binary_path_regression": binary_path_regression(),
        "unrestricted_energy_boundary": unrestricted_energy_boundary(),
        "forest_potential_identity": [
            {"b_exponent": exponent[0], "c_exponent": exponent[1],
             "coefficient": str(coefficient)}
            for exponent, coefficient in sorted(potential_left.items())],
        "star_head_hubs": star_hubs,
        "general_357_head_hubs": general_hubs,
        "head_primes": list(HEAD_PRIMES), "minimum_each_head_height": 1,
        "K0": str(k_zero), "C0": str(c_zero),
        "ternary_finite_height": {
            "r": "3^(-H)", "density": "(1-r)/2", "chi_sum": "2-(H+2)*r",
            "chi_factor": "5-2*H*r/(1-r)", "cylinder_factor": "2",
            "base_H0_sum": "0", "recurrence_increment_coefficients": recurrence_coefficients,
            "exact_examples": profiles},
        "prime_cutoff": 4000, "rounding_scale": scale,
        "tail_primes_to_cutoff": selected, "prime_count": len(selected),
        "ceiling_sum": ceiling_sum, "odd_integer_tail_bound": str(odd_tail),
        "prime_square_upper": str(prime_square_upper),
        "matching_pair_factor": str(pair_factor), "matching_loss_upper": str(matching_loss),
        "matching_retained_lower": str(retained), "singleton_delta": str(delta),
        "singleton_loss_upper": str(singleton_loss),
        "residual_crossing_threshold": str(residual_threshold),
        "two_prime_raw_crossing_threshold": str(pair_raw_threshold),
        "weighted_edge_threshold": str(edge_threshold),
        "dense_comparison_primes": dense_primes, "dense_comparison_edges": 210,
        "dense_pair_reciprocal_sum": str(dense_sum),
        "dense_comparison_actual_E": "0", "dense_comparison_actual_J": str(dense_actual_budget),
        "dense_comparison_violates_simplified_uniform_budget": True,
        "dense_comparison_satisfies_full_block_criterion": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).with_name("star_block_obstruction_certificate.json"))
    parser.add_argument("--write-certificate", action="store_true")
    args = parser.parse_args()
    data = certificate()
    if args.write_certificate:
        args.certificate.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    else:
        require(json.loads(args.certificate.read_text(encoding="utf-8")) == data,
                "fixed certificate matches recomputed exact values")
    print(json.dumps({"result": "PASS", "minimum_each_head_height": 1,
                      "K0_decimal": float(F(data["K0"])), "C0_decimal": float(F(data["C0"])),
                      "prime_square_upper": data["prime_square_upper"],
                      "matching_retained_lower": data["matching_retained_lower"],
                      "residual_crossing_threshold": data["residual_crossing_threshold"],
                      "weighted_edge_threshold": data["weighted_edge_threshold"],
                      "dense_comparison_satisfies_full_block_criterion": True,
                      "general_357_component3_prime31_loss": data["general_357_head"]["component_at_most_three_prime_31_loss_upper"],
                      "general_357_degree2_prime37_loss": data["general_357_head"]["maximum_degree_two_prime_37_loss_upper"],
                      "prime31_scalar_Gamma_cube_obstruction": data["general_357_head"]["prime_31_common_delta_scalar_boundary"]["Gamma_times_lower_exceeds_33_over_50_cubed"],
                      "prime31_scalar_cylinder_cube_obstruction": data["general_357_head"]["prime_31_common_delta_scalar_boundary"]["cylinder_times_lower_exceeds_17_over_50_cubed"],
                      "star_forest_loss_bounds": {row["head"]: row["loss_upper"] for row in data["star_forest"]},
                      "arbitrary_forest_loss_bounds": {row["head"]: row["loss_upper"] for row in data["arbitrary_forest"]},
                      "feedback_vertex_loss_bounds": {row["head"]: row["loss_upper"] for row in data["feedback_vertex"]},
                      "local_parent_capped_kernel_loss_bounds": {row["head_and_graph"]: row["loss_upper"] for row in data["local_parent_capped_kernel"]},
                      "rank_two_tail_loss_bounds": {row["head"]: row["loss_upper"] for row in data["rank_two_tail"]["rows"]},
                      "rank_three_tail_loss_bounds": {row["head"]: row["loss_upper"] for row in data["rank_three_tail"]["rows"]},
                      "finite_head_supported_Gamma_bounds": {row["period_bound"]: row["Gamma_bound"] for row in data["finite_head_supported_laws"]},
                      "local_kernel_crt_regression_cases": data["local_kernel_crt_regression"]["cases"],
                      "binary_path_regression_cases": data["binary_path_regression"]["cases"],
                      "pendant_degree_two_core_loss": data["pendant_degree_two_core"]["loss_upper"],
                      "star_vertex_cover_8_loss": data["star_head_hubs"]["vertex_cover_loss_upper"],
                      "general_vertex_cover_6_loss": data["general_357_head_hubs"]["vertex_cover_loss_upper"],
                      "scope": "Exact constants; arbitrary-height lifting is an ordinary proof."}))


if __name__ == "__main__":
    main()
