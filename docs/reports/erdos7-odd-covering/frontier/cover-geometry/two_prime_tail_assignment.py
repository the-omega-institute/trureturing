#!/usr/bin/env python3
"""Exact original-cylinder controls for two-prime owned early trimming.

The cyclic moderate-prime fixture verifies its own finite budgets. It does
not instantiate the theorem's astronomical uniform prime cutoff.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import prod
from pathlib import Path
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def crt(parts):
    parts = [(a % m, m) for a, m in parts if m > 1]
    m = prod(q for a, q in parts)
    return sum(a * (m // q) * pow(m // q, -1, q) for a, q in parts) % m


def offset(p, q):
    """Smallest s with q^s >= p^2; p is the higher numerical prime."""
    s, power = 0, 1
    while power < p * p:
        s += 1
        power *= q
    return s


def normalise_prefixes(p, prefixes):
    retained = set()
    for f, a in sorted(set((f, a % p ** f) for f, a in prefixes)):
        if not any((g, a % p ** g) in retained for g in range(1, f + 1)):
            retained.add((f, a))
    return tuple(sorted(retained))


class Kernel:
    def __init__(self, p, J, prefixes):
        self.p, self.J = p, J
        self.forbidden = normalise_prefixes(p, prefixes)
        self.deleted = sum((F(1, p ** f) for f, a in self.forbidden), F())
        self.survival = 1 - self.deleted
        require(self.survival > 0, "actual owned-cylinder complement nonempty")

    @lru_cache(maxsize=None)
    def remaining(self, f, a):
        a %= self.p ** f
        for g, b in self.forbidden:
            if g <= f and a % self.p ** g == b:
                return F()
        removed = sum((F(1, self.p ** g) for g, b in self.forbidden
                       if g > f and b % self.p ** f == a), F())
        mass = F(1, self.p ** f) - removed
        require(mass >= 0, "laminar cylinder accounting")
        return mass

    def probability(self, f, a):
        return self.remaining(f, a) / self.survival

    def witness(self):
        a = 0
        for f in range(1, self.J + 1):
            candidates = [a + digit * self.p ** (f - 1) for digit in range(self.p)]
            a = next(b for b in candidates if self.remaining(f, b) > 0)
        require(all(a % self.p ** f != b for f, b in self.forbidden), "actual prime-power witness")
        return a


HEAD = {5: 0, 7: 0, 25: 21, 35: 34, 49: 48,
        175: 173, 245: 242, 1225: 241}
MU = {1: 3, 106: 3, 456: 1, 211: 2, 561: 2, 316: 1, 666: 3,
      2: 3, 107: 3, 212: 3, 317: 3, 422: 3,
      3: 3, 108: 3, 213: 3, 318: 3, 423: 3,
      4: 3, 109: 3, 214: 3, 319: 3, 424: 3}


def verify():
    # Independent full-period comparison for the laminar counter used below.
    laminar_checks = 0
    for prefixes in [[], [(1, 0), (2, 0), (3, 125), (2, 6), (3, 31)],
                     [(2, 1), (2, 6), (3, 3), (3, -1)],
                     [(1, 1), (1, 2), (1, 3), (1, 4), (3, 0)]]:
        small = Kernel(5, 3, prefixes)
        survivors = [x for x in range(125)
                     if all(x % 5 ** f != a % 5 ** f for f, a in prefixes)]
        require(small.survival == F(len(survivors), 125), "enumerated union mass")
        for f in range(4):
            for a in range(5 ** f):
                count = sum(x % 5 ** f == a for x in survivors)
                require(small.remaining(f, a) == F(count, 125), "enumerated raw cylinder mass")
                require(small.probability(f, a) == F(count, len(survivors)),
                        "enumerated conditioned cylinder mass")
                laminar_checks += 1
    D, H = 9, 2
    P = [101, 103, 107]
    J = {p: 5 for p in P}
    E = {101: 0, 103: 1, 107: 0}
    edges = [(q, p) for q, p in combinations(P, 2)]
    shifts = {(q, p): offset(p, q) for q, p in edges}
    require(set(shifts.values()) == {3}, "the uniform construction's actual ownership offset")
    originals = dict(HEAD)
    for e in range(1, H + 1):
        originals[3 ** e] = 3 ** (e - 1) - 1
    rows = []

    def insert(e, i, j, tail):
        a = 5 ** i * 7 ** j
        prime_sum = sum(p for p, f in tail)
        exponent_sum = sum(f for p, f in tail)
        head_value = 1 + ((e + i + 2 * j + exponent_sum + prime_sum % 4) % 4)
        base = 30 * e + (8 if len(tail) == 2 else 0) + i + j + exponent_sum
        phases = [(p, f, (base + p * (e + i + j + f + exponent_sum)) % p ** f)
                  for p, f in tail]
        parts = [(head_value, a), *((beta, p ** f) for p, f, beta in phases)]
        if e:
            parts.append((2 * 3 ** (e - 1) - 1, 3 ** e))
        d = 3 ** e * a * prod(p ** f for p, f in tail)
        residue = crt(parts)
        require(d not in originals and d > 1 and d % 2, "distinct odd original labels")
        originals[d] = residue
        rows.append({"d": d, "residue": residue, "e": e, "a": a,
                     "alpha": residue % a, "phases": phases})

    for e, i, j in product(range(H + 1), range(3), range(3)):
        for p in P:
            for f in range(1, J[p] + 1):
                insert(e, i, j, [(p, f)])
        for q, p in edges:
            for g, f in product(range(1, J[q] + 1), range(1, J[p] + 1)):
                insert(e, i, j, [(q, g), (p, f)])

    comparable = 0
    for d, m in combinations(sorted(originals), 2):
        if m % d == 0:
            require((originals[m] - originals[d]) % d != 0, "all comparable original APs disjoint")
            comparable += 1
    require(len(originals) == 2440 and sum(MU.values()) == 60, "actual inventory and head probability")
    require(all(all(x % d != a for d, a in HEAD.items()) for x in MU), "actual head support")

    budget = {p: D * (E[p] + 1) * sum((F(1, p ** f) for f in range(1, J[p] + 1)), F()) for p in P}
    ownership_count_checks = 0
    for q, p in edges:
        s = shifts[q, p]
        high = sum((min(J[q], f + s) * F(1, p ** f) for f in range(1, J[p] + 1)), F())
        low = sum((min(J[p], max(0, g - s - 1)) * F(1, q ** g) for g in range(1, J[q] + 1)), F())
        direct_high = sum((F(1, p ** f) for f, g in product(range(1, J[p] + 1), range(1, J[q] + 1)) if g <= f + s), F())
        direct_low = sum((F(1, q ** g) for f, g in product(range(1, J[p] + 1), range(1, J[q] + 1)) if g > f + s), F())
        require(high == direct_high and low == direct_low > 0, "both ownership arms, exact finite exponent accounting")
        require(high <= F(p, (p - 1) ** 2) + F(s, p - 1), "high-owner all-height upper")
        require(low <= F(1, q ** s * (q - 1) ** 2), "low-owner all-height upper")
        budget[p] += D * (E[p] + 1) * high
        budget[q] += D * (E[p] + 1) * low
        ownership_count_checks += J[p] * J[q]
    delta = {p: 1 - budget[p] for p in P}
    require(all(d > 0 for d in delta.values()), "fixture's finite permissive budgets")

    owned = {(x, p): [] for x in MU for p in P}
    owners = []
    arms = Counter()
    for row in rows:
        phases = row['phases']
        if len(phases) == 1:
            p, f, beta = phases[0]
            cut, owner = E[p], (p, f, beta)
            arm = 'singleton'
        else:
            (q, g, beta_q), (p, f, beta_p) = phases
            cut = E[p]
            if g <= f + shifts[q, p]:
                owner, arm = (p, f, beta_p), 'higher_prime'
            else:
                owner, arm = (q, g, beta_q), 'lower_prime'
        owners.append((cut, owner))
        if row['e'] <= cut:
            arms[arm] += 1
            p, f, beta = owner
            for x in MU:
                if x % row['a'] == row['alpha']:
                    owned[x, p].append((f, beta))
    require(arms['higher_prime'] > 0 and arms['lower_prime'] > 0, "both assignment arms used by actual originals")
    kernels = {(x, p): Kernel(p, J[p], prefixes) for (x, p), prefixes in owned.items()}
    require(all(k.survival >= delta[p] for (x, p), k in kernels.items()), "one actual kernel within every budget")
    require(all(k.probability(0, 0) == 1 for k in kernels.values()), "every kernel normalized")
    marginals = {x: F(w, 60) * prod(kernels[x, p].probability(0, 0) for p in P)
                 for x, w in MU.items()}
    require(all(marginals[x] == F(w, 60) for x, w in MU.items())
            and sum(marginals.values()) == 1, "one law preserves the entire head marginal")

    # This defines ONE finite law: mu(x) times the three conditional kernels.
    # No joint period enumeration or per-test reoptimization is used.
    phase_checks = 0
    full_early_checks = 0
    load_single = {p: F() for p in P}
    load_pair = {edge: F() for edge in edges}
    for row, (cut, owner) in zip(rows, owners):
        mass = F()
        for x, numerator in MU.items():
            if x % row['a'] != row['alpha']:
                continue
            factors = []
            for p, f, beta in row['phases']:
                prob = kernels[x, p].probability(f, beta)
                require(0 <= prob <= F(1, p ** f) / delta[p], "simultaneous conditional cylinder caps")
                phase_checks += 1
                factors.append(prob)
            joint = prod(factors)
            if row['e'] <= cut:
                require(joint == 0, "owned early full original event vanishes")
                full_early_checks += 1
            mass += F(numerator, 60) * joint
        if row['e']:
            contribution = F(1, 3 ** (row['e'] - 1)) * mass
            if len(row['phases']) == 1:
                load_single[row['phases'][0][0]] += contribution
            else:
                edge = tuple(t[0] for t in row['phases'])
                load_pair[edge] += contribution
    require(all(v > 0 for v in load_single.values()) and all(v > 0 for v in load_pair.values()),
            "positive actual late loads in every vertex and edge")
    R = {p: sum((F(1, p ** f) for f in range(1, J[p] + 1)), F()) for p in P}
    tail_weight = {p: F(3, 2 * 3 ** E[p]) * (1 - F(1, 3 ** (H - E[p]))) for p in P}
    bound_single = {p: D * tail_weight[p] * R[p] / delta[p] for p in P}
    bound_pair = {(q, p): D * tail_weight[p] * R[q] * R[p] / (delta[q] * delta[p]) for q, p in edges}
    require(all(load_single[p] <= bound_single[p] for p in P), "single-prime late bounds")
    require(all(load_pair[edge] <= bound_pair[edge] for edge in edges), "same-law paired late bounds")

    witness_checks = 0
    witness_samples = []
    for x in MU:
        coordinate = {p: kernels[x, p].witness() for p in P}
        point = crt([(x, 1225), *((coordinate[p], p ** J[p]) for p in P)])
        for d, a in originals.items():
            if d % 3:
                require(point % d != a, "actual full cofactor witness avoids every 3-free original")
                witness_checks += 1
        if x in [1, 106, 2]:
            witness_samples.append({'head': x, 'outside_coordinates': coordinate})

    # Failure of ignoring paired constraints: singleton-only kernels retain
    # a positive mass on an actual 3-free pair original.
    solo = {(x, p): [] for x in MU for p in P}
    for row in rows:
        if len(row['phases']) != 1:
            continue
        p, f, beta = row['phases'][0]
        if row['e'] <= E[p]:
            for x in MU:
                if x % row['a'] == row['alpha']:
                    solo[x, p].append((f, beta))
    solo = {key: Kernel(key[1], J[key[1]], value) for key, value in solo.items()}
    missed = next(row for row in rows if row['e'] == 0 and row['a'] == 1 and len(row['phases']) == 2)
    missed_mass = sum((F(w, 60) * prod(solo[x, p].probability(f, beta) for p, f, beta in missed['phases'])
                      for x, w in MU.items()), F())
    require(missed_mass > 0, "actual paired-support countercontrol")

    # The uniform astronomical-cutoff theorem is proved in the companion note.
    # These exact constants check its final scalar comparison, not prime counts.
    scalar = F(145138176, 3 ** 20)
    require(scalar < F(1, 24) < F(1, 4), "explicit all-D tail constant")
    require(F(16, 3 ** 20) < 1, "D^4/3^(20D) monotonic ratio bound")
    result = {
        'scope': 'Actual cyclic finite-budget control; ordinary mathematics, no Lean, no claim that moderate primes meet the uniform large cutoff.',
        'Q': 1225, 'D': D, 'H': H, 'outside_primes': P, 'heights': J, 'cuts': E,
        'graph_edges': edges, 'graph_cycle_rank': len(edges) - len(P) + 1,
        'offsets': {f'{q}-{p}': s for (q, p), s in shifts.items()},
        'original_classes': len(originals), 'comparable_disjoint_pairs': comparable,
        'four_and_five_prime_support_examples': {
            str(arity): next(row['d'] for row in rows if row['e'] == 1
                             and row['a'] == head_part and len(row['phases']) == 2)
            for arity, head_part in [(4, 5), (5, 35)]},
        'ownership_exponent_checks': ownership_count_checks, 'actual_early_owned_classes': dict(arms),
        'uniform_deleted_budget': {p: str(v) for p, v in budget.items()},
        'uniform_kernel_survival_lower': {p: str(v) for p, v in delta.items()},
        'head_law_atoms': len(MU), 'head_marginal_preserved': True,
        'kernel_normalization_checks': len(kernels),
        'enumerated_laminar_cylinder_checks': laminar_checks,
        'literal_conditional_phase_checks': phase_checks, 'early_full_event_zero_checks': full_early_checks,
        'full_cofactor_witness_membership_checks': witness_checks,
        'single_late_loads': {p: str(v) for p, v in load_single.items()},
        'pair_late_loads': {f'{q}-{p}': str(v) for (q, p), v in load_pair.items()},
        'single_late_upper': {p: str(v) for p, v in bound_single.items()},
        'pair_late_upper': {f'{q}-{p}': str(v) for (q, p), v in bound_pair.items()},
        'sample_kernels': [{'head': x, 'prime': p, 'minimal_forbidden_prefixes': len(kernels[x, p].forbidden),
                            'survival': str(kernels[x, p].survival)} for x in [1, 106, 2] for p in P],
        'witness_samples': witness_samples,
        'singleton_only_failure': {'original_modulus': missed['d'], 'original_residue': missed['residue'],
                                   'positive_forbidden_mass': str(missed_mass)},
        'uniform_cutoff': {'formula': 'B=3^(2560 D^2)', 'D9_exponent': 207360,
                           'all_D_tail_upper': str(scalar), 'comparison': '< 1/24 < 1/4'},
    }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify()
    payload = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload, encoding='utf-8')
        print(json.dumps({'result': 'PASS', 'original_classes': result['original_classes'],
                          'owned_arms': result['actual_early_owned_classes'],
                          'phase_checks': result['literal_conditional_phase_checks'],
                          'output': str(args.output)}, indent=2))
    else:
        print(payload, end='')


if __name__ == '__main__':
    main()
