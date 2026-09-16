#!/usr/bin/env python3
"""Check the nine-cell budget, density certificate and four-prime head.

Python 3.9+ standard library only. No solver, network, external imports,
or absolute paths. The accompanying proof establishes the probabilistic
meaning of the input profile and three density constraints; this program
checks their infinite envelope arithmetic and sparse rational dual identity,
then propagates the resulting head and verifies the prime-71/73 continuation.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def subsets(s):
    for n in range(len(s) + 1):
        yield from combinations(s, n)


def parse_profile(data):
    return {(() if key == "1" else tuple(map(int, key.split("*")))): F(value)
            for key, value in data.items()}


def expected_head_profile():
    """Propagate the proved two-prime R bounds through the same-law recurrence."""
    primes = (3, 5, 7)
    pair_r = {(3, 5): F(15, 7), (3, 7): F(21, 13), (5, 7): F(9, 14)}
    pure_c = {p: F(p - 1, p - 2) for p in primes}
    pairs = {}
    for pair in combinations(primes, 2):
        survival = 1 - prod(F(1, p - 2) for p in pair)
        ordinary = {t: (prod(pure_c[p] for p in t) / survival if t else F(1))
                    for t in subsets(pair)}
        first = {t: ordinary[t] for t in subsets(pair) if 3 in t}
        if 3 in pair:
            q = next(p for p in pair if p != 3)
            first[(3,)] = min(first[(3,)], F(6 * (q - 2), 3 * q - 8))
        pairs[pair] = ordinary, first
    candidates = []
    for p in primes:
        pair = tuple(q for q in primes if q != p)
        old_c, old_b = pairs[pair]
        survival = 1 - pair_r[pair] / (p - 2)
        require(survival > 0, "last-prime survivor bound is not positive")
        c, b = {(): F(1)}, {}
        for support in subsets(primes):
            if not support:
                continue
            previous = tuple(q for q in support if q != p)
            factor = (pure_c[p] if p in support else F(1)) / survival
            c[support] = old_c[previous] * factor
            if 3 in support:
                b[support] = (old_c[previous] if p == 3 else old_b[previous]) * factor
        candidates.append((c, b))
    return ({t: min(c[t] for c, _ in candidates) for t in subsets(primes)},
            {t: min(b[t] for _, b in candidates) for t in subsets(primes) if 3 in t})


def envelope_sums(primes, c, b):
    """Exact R and K from ordinary and first-ternary-projection coefficients."""
    cutoffs = {}
    for p in primes:
        others = tuple(q for q in primes if q != p)
        ratios = [c[tuple(sorted(t + (p,)))] / c[t] for t in subsets(others)]
        if p == 3:
            ratios += [3 * c[t] / b[t] for t in b]
        else:
            ratios += [b[tuple(sorted(t + (p,)))] / b[t]
                       for t in subsets(others) if 3 in t]
        cutoff = 1 if p == 3 else 0
        while p ** (cutoff + 1) < max(ratios):
            cutoff += 1
        cutoffs[p] = cutoff

    total = moment = F(0)
    for states in product(*(range(cutoffs[p] + 2) for p in primes)):
        exponents = dict(zip(primes, states))
        high = tuple(p for p in primes if exponents[p] == cutoffs[p] + 1)
        low = tuple(p for p in primes if 0 < exponents[p] <= cutoffs[p])
        terms = []
        for t in subsets(low):
            support = tuple(sorted(high + t))
            terms.append(c[support] / prod(p ** exponents[p] for p in t))
            if 3 in t and 3 not in high:
                terms.append(b[support] /
                             (3 * prod(p ** exponents[p] for p in t if p != 3)))
        cell = weighted_cell = min(terms)
        for p in high:
            cell *= F(1, p ** cutoffs[p] * (p - 1))
            weighted_cell *= F((2 * cutoffs[p] + 3) * (p - 1) + 2,
                               p ** cutoffs[p] * (p - 1) ** 2)
        for p in low:
            weighted_cell *= 2 * exponents[p] + 1
        total += cell
        moment += weighted_cell
    return total - 1, moment, cutoffs


def budget_vertices(dimension, budget):
    yield (F(0),) * dimension
    for j in range(dimension):
        yield tuple(budget if i == j else F(0) for i in range(dimension))


def nine_cell_bounds(q):
    """Evaluate the full 1,296-vertex relaxation and both missing-class cases."""
    roots = (0, 0, 1, 1, 1)
    y, a = F(1, q - 1), F(3 * q - 1, (q - 1) ** 2)
    best_r = best_k = F(0)
    count = 0
    for z, deficits, alpha, beta, t in product(
            (1 - y, F(1)), budget_vertices(5, F(1, 2)),
            budget_vertices(2, y), budget_vertices(5, y),
            budget_vertices(5, y / 18)):
        w = tuple(1 - d for d in deficits)
        x = sum(w) / 9
        cells = tuple(w[j] * (z - alpha[roots[j]] - beta[j]) / 9 - t[j]
                      for j in range(5))
        s = sum(cells)
        require(min(cells) >= (1 - 4 * y) / 18, "nine-cell positivity bound failed")
        require(s >= x * z - y / 2 >= F(1, 2) - y > 0,
                "nine-cell denominator bound failed")
        root_mass = max(sum(cells[j] for j in range(5) if roots[j] == r)
                        for r in range(2))
        cell_mass = max(cells)
        best_r = max(best_r, (root_mass + cell_mass + z / 18 + x * y + y / 2) / s)
        best_k = max(best_k, 1 + (3 * root_mass + 5 * cell_mass + 4 * z / 9
                                  + a * x + 2 * a) / s)
        count += 1
    require(count == 1296, "nine-cell vertex count mismatch")

    # Absence of modulus 3 gives x>=5/6. Presence of modulus 3 with no
    # effective modulus-9 exclusion gives x>=11/18. The latter lower bound
    # covers both cases; the raw fractions decrease in x and z.
    x, z = F(11, 18), 1 - y
    denominator = x * z - y / 2
    require(denominator > 0, "missing-class denominator is not positive")
    missing_r = (z / 2 + x * y + y / 2) / denominator
    missing_k = 1 + (2 * z + a * x + 2 * a) / denominator
    require(missing_r <= best_r and missing_k <= best_k,
            "missing-class branch exceeds the stated budget bound")
    return best_r, best_k, {
        "vertices": count,
        "R_bound": str(best_r), "K_bound": str(best_k),
        "missing_class_R_bound": str(missing_r),
        "missing_class_K_bound": str(missing_k),
    }


def head_recurrence(primes, pair_bounds, density_bound):
    """Keep cylinder envelopes separate from bounds on their actual sums."""
    profiles = {(): ({(): F(1)}, {})}
    metrics = {(): (F(0), F(1))}
    for size in range(1, len(primes) + 1):
        for support in combinations(primes, size):
            candidates = []
            for p in support:
                old = tuple(q for q in support if q != p)
                if old not in profiles:
                    continue
                survival = 1 - metrics[old][0] / (p - 2)
                if survival <= 0:
                    continue
                old_c, old_b = profiles[old]
                c, b = {(): F(1)}, {}
                for t in subsets(support):
                    if not t:
                        continue
                    previous = tuple(q for q in t if q != p)
                    factor = (F(p - 1, p - 2) if p in t else F(1)) / survival
                    c[t] = old_c[previous] * factor
                    if 3 in t:
                        b[t] = (old_c[previous] if p == 3 else old_b[previous]) * factor
                candidates.append((c, b))
            require(candidates, "no certified survivor normalization for a subset")
            c = {t: min(cc[t] for cc, _ in candidates) for t in subsets(support)}
            b = {t: min(bb[t] for _, bb in candidates)
                 for t in subsets(support) if 3 in t}
            if size == 2 and 3 in support:
                q = next(p for p in support if p != 3)
                b[(3,)] = min(b[(3,)], F(6 * (q - 2), 3 * q - 8))
            profiles[support] = c, b
            r, k, _ = envelope_sums(support, c, b)
            if size == 2 and 3 in support:
                joint_r, joint_k = pair_bounds[next(p for p in support if p != 3)]
                r, k = min(r, joint_r), min(k, joint_k)
            if support == (3, 5, 7):
                r = min(r, density_bound)
            metrics[support] = r, k
    return profiles, metrics


def main():
    data = json.loads(Path(__file__).with_name("joint_density_certificate.json").read_text())
    primes = tuple(data["prime_support"])
    require(primes == (3, 5, 7), "unexpected prime support")
    c = parse_profile(data["ordinary_profile"])
    b = parse_profile(data["first_ternary_fibre_profile"])
    require(set(c) == set(subsets(primes)), "ordinary profile support mismatch")
    require(set(b) == {t for t in subsets(primes) if 3 in t},
            "first-ternary profile support mismatch")
    require(c[()] == 1 and all(v > 0 for v in list(c.values()) + list(b.values())),
            "profile coefficients must be positive and unit-normalized")
    require((c, b) == expected_head_profile(), "profile does not match the proved recurrence")

    pair_bounds, pair_details = {}, {}
    for q, expected in {
            5: (F(15, 7), F(173, 12)),
            7: (F(21, 13), F(19, 2)),
            11: (F(33, 25), F(181, 25)),
    }.items():
        r, k, detail = nine_cell_bounds(q)
        require((r, k) == expected, "nine-cell rational extremum mismatch")
        pair_bounds[q], pair_details[str(q)] = (r, k), detail

    old_r, old_k, cutoffs = envelope_sums(primes, c, b)
    require(old_r == F(data["old_envelope_R"]), "old infinite envelope mismatch")
    require(old_k == F(749, 18), "three-prime raw weighted envelope mismatch")
    # On pure 3^e with e>=2, the ordinary term is smaller than the unit
    # and first-ternary caps already at e=2, and decreases thereafter.
    require(c[(3,)] / 9 <= min(F(1), b[(3,)] / 3),
            "pure ternary tail is not given by the ordinary profile")
    pure_3_tail = c[(3,)] * F(1, 6)
    require(c[(5,)] / 5 <= 1, "pure quinary sum has an active projection cap")
    pure_5_sum = c[(5,)] * F(1, 4)
    require(pure_3_tail == F(data["removed_pure_3_tail"]), "ternary sum mismatch")
    require(pure_5_sum == F(data["removed_pure_5_sum"]), "quinary sum mismatch")
    remainder = old_r - pure_3_tail - pure_5_sum
    require(remainder == F(data["remaining_envelope_sum"]), "remainder mismatch")

    # Reconstruct the three inequality coefficients from their proved
    # formulas; the JSON names alone are not accepted as evidence.
    require(data["variable_order"] == ["t", "v35", "v37", "v57"],
            "density variable order mismatch")
    theta_35_min = 1 - F(1, 3 - 2) * F(1, 5 - 2)
    alpha_35 = 1 - F(15, 7) / (7 - 2)
    global_coefficient = 2 + prod(F(1, p - 2) for p in primes)
    expected_rows = (
        ([theta_35_min, -F(1), F(0), F(0)], F(0)),
        ([F(0), alpha_35, F(0), F(0)], F(1)),
        ([-global_coefficient, F(1), F(1), F(1)], F(1)),
    )
    require(len(data["dual"]) == len(expected_rows), "sparse dual length mismatch")
    aggregate = [F(0)] * 4
    rhs = F(0)
    for item, (expected_row, expected_rhs) in zip(data["dual"], expected_rows):
        row = list(map(F, item["coefficients"]))
        bound, weight = F(item["upper_bound"]), F(item["weight"])
        require(row == expected_row and bound == expected_rhs, "density row mismatch")
        require(weight >= 0, "negative dual weight")
        aggregate = [a + weight * v for a, v in zip(aggregate, row)]
        rhs += weight * bound
    objective = [F(0), F(0), F(1, 3), F(1, 3)]
    require(aggregate == objective == list(map(F, data["objective_coefficients"])),
            "sparse dual does not reproduce the target objective")
    require(rhs == F(data["objective_upper_bound"]), "dual upper bound mismatch")
    improved_r = remainder + rhs
    require(improved_r == F(data["improved_R_bound"]), "improved R mismatch")
    require(improved_r == F(1649, 360) and improved_r < old_r,
            "certificate does not prove the claimed strict improvement")

    head_primes = tuple(data["head_prime_support"])
    require(head_primes == (3, 5, 7, 11), "unexpected four-prime support")
    profiles, metrics = head_recurrence(head_primes, pair_bounds, improved_r)
    require(len(profiles) == 16, "a four-prime predecessor is missing")
    require(profiles[primes] == (c, b), "density certificate has a different input profile")
    final_r, final_k = metrics[head_primes]
    require(final_r == F(data["head_R_bound"]), "four-prime R bound mismatch")
    require(final_k == F(data["head_Gamma_bound"]), "four-prime Gamma bound mismatch")
    require(final_k == F(187719326, 1723053) < F(108945765, 1000000),
            "four-prime head exceeds the displayed bound")
    raw_r, raw_k, head_cutoffs = envelope_sums(head_primes, *profiles[head_primes])
    require((raw_r, raw_k) == (final_r, final_k),
            "the final four-prime bound should equal its profile envelope")
    ratio, bridge = final_k, []
    expected_steps = ((71, F(53, 200)), (73, F(27, 100)))
    require(len(data["bridge"]) == len(expected_steps), "bridge step count mismatch")
    for item, (p, delta) in zip(data["bridge"], expected_steps):
        require(item["prime"] == p and F(item["delta"]) == delta, "bridge input mismatch")
        survivor_fraction = 1 - ratio / (4 * delta * (1 - delta) * (p - 1) ** 2)
        require(survivor_fraction > 0, "bridge survivor fraction is not positive")
        ratio *= (1 + F(3 * p - 1, (p - 1) ** 2) / (1 - delta)) / survivor_fraction
        require(survivor_fraction == F(item["survivor_fraction_lower_bound"]),
                "bridge denominator mismatch")
        require(ratio == F(item["continued_ratio_upper_bound"]), "bridge ratio mismatch")
        bridge.append({"prime": p, "survivor_fraction_lower_bound": str(survivor_fraction),
                       "continued_ratio_upper_bound": str(ratio)})
    require(ratio < F(138877, 1000), "continued ratio exceeds the tail seed")
    print(json.dumps({
        "nine_cell_bounds": pair_details,
        "prime_support": primes,
        "old_envelope_R": str(old_r),
        "cutoffs": cutoffs,
        "sparse_dual_nonzero_weights": len(data["dual"]),
        "dual_residual": list(map(str, (a - v for a, v in zip(aggregate, objective)))),
        "replacement_upper_bound": str(rhs),
        "improved_R_bound": str(improved_r),
        "improved_R_decimal": float(improved_r),
        "head_prime_support": head_primes,
        "head_R_bound": str(final_r),
        "head_Gamma_bound": str(final_k),
        "head_Gamma_decimal": float(final_k),
        "head_cutoffs": head_cutoffs,
        "bridge": bridge,
        "continued_ratio_decimal": float(ratio),
        "tail_seed": "138877/1000",
        "scope": "Exact infinite sums and a fixed nonnegative rational dual identity. "
                 "The accompanying proof establishes the common survivor-law model. "
                 "No Lean kernel certification is claimed.",
    }, indent=2))


if __name__ == "__main__":
    main()
