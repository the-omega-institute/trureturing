"""Exact single-axis moment certificate for one globally phased old dictionary.

Standard-library rational arithmetic; all checks survive Python -O. The
general comparison is proved in report769. This verifies its literal finite
premises, not universal dictionary feasibility or unrestricted Erdos #7.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from math import comb, prod
from pathlib import Path


D = tuple(d for d in range(1, 316) if 315 % d == 0)
P = (11, 13, 17, 19, 23)
S = tuple(p - 1 for p in P)
INPUT_SHA256 = '0ecdff7f924d4b47c2654401bf424afe65e9b2f42cebfcc86698531bfe58da18'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def kappa(d):
    return prod((F(p, p - 1) for p, top in ((3, 9), (5, 5), (7, 7))
                 if d % top == 0), start=F(1)) - 1


def elementary(values, degree):
    return sum((prod(term, start=F(1)) for term in combinations(values, degree)), F(0))


def coefficients():
    result = {}
    for j in range(5):
        for k in range(1, 6):
            value = F(S[j] ** (k - 1), k) * elementary(
                [F(1, S[i]) for i in range(5) if i != j], k - 1)
            direct = sum((F(S[j] ** k, k * prod(S[i] for i in subset))
                          for subset in combinations(range(5), k) if j in subset), F(0))
            need(value == direct > 0, 'Positive coefficient equals full subset sum')
            result[j, k] = value
    return result


def cylinder_cap(rows, values, d):
    bins = [F(0)] * d
    for x, value in zip(rows, values):
        bins[x % d] += value
    top = max(bins)
    return top, bins.index(top)


def joint_cost(rows, lower, weights):
    need(len(rows) == len(weights) and all(w >= 0 for w in weights), 'Row weights')
    need(sum(weights) > 0 and all(w == 0 or min(lower[x]) > 0
                                 for x, w in zip(rows, weights)), 'Positive denominator support')
    caps, total = [], F(0)
    for mask in range(32):
        axes = [j for j in range(5) if mask & (1 << j)]
        values = [F(w, prod(lower[x][j] for j in axes)) if w else F(0)
                  for x, w in zip(rows, weights)]
        for d in D:
            coefficient = kappa(d) + (len(axes) >= 2)
            if coefficient:
                cap, witness = cylinder_cap(rows, values, d)
                total += coefficient * cap
                caps.append([d, mask, str(cap), witness])
    need(len(caps) == 372, 'All nonzero joint query slots')
    return total, caps


def marginal_cost(rows, lower, weights, coeff):
    caps, total = [], F(0)
    for d in D:
        if kappa(d):
            cap, witness = cylinder_cap(rows, list(map(F, weights)), d)
            total += kappa(d) * cap
            caps.append([d, -1, 0, str(cap), witness])
    for j in range(5):
        for k in range(1, 6):
            values = [F(w, lower[x][j] ** k) if w else F(0) for x, w in zip(rows, weights)]
            for d in D:
                beta = kappa(d) + (k >= 2)
                if beta:
                    cap, witness = cylinder_cap(rows, values, d)
                    total += beta * coeff[j, k] * cap
                    caps.append([d, j, k, str(cap), witness])
    need(len(caps) == 300, 'All nonzero single-axis query slots')
    return total, caps


def calculate():
    path = Path(__file__).with_name('fibre_credit_depth_two_single_axis_input.json')
    raw = path.read_bytes()
    need(sha256(raw).hexdigest() == INPUT_SHA256, 'Pinned literal input')
    data = json.loads(raw)
    need(data['divisor_order'] == list(D[1:]), 'Complete divisor order')
    core = data['core_phases']
    phases = data['singleton_old_phases']
    need(len(core) == 11 and len(phases) == 5 and all(len(a) == 11 for a in phases),
         'One complete core and five singleton old-phase dictionaries')
    need(all(type(a) is int and 0 <= a < d for row in [core] + phases
             for d, a in zip(D[1:], row)), 'Literal globally fixed phases')
    rows = [x for x in range(315) if all(x % d != a for d, a in zip(D[1:], core))]
    need(len(rows) == 74, 'Actual survivor count')
    lists = [data['weight_zero_rows'], data['weight_one_rows']]
    need(all(all(type(x) is int for x in values) and values == sorted(set(values))
             for values in lists), 'Unique ordered integer row labels')
    zero, one = map(set, lists)
    need(len(zero) == 12 and len(one) == 22 and not zero & one
         and zero | one <= set(rows), 'Disjoint supported weight lists')
    weights = [0 if x in zero else 1 if x in one else 2 for x in rows]
    need(sum(weights) == 102 and weights.count(2) == 40, 'Integer mass total')
    hits = {x: [sum(x % d == a for d, a in zip(D[1:], row)) for row in phases] for x in rows}
    lower = {x: [S[j] - hits[x][j] for j in range(5)] for x in rows}
    need(all(min(v) > 0 for v in lower.values()), 'Every displayed row is admissible')
    numerical = [[d, a] for d, a in zip(D[1:], core)]
    fibre_checks, strict_rows = 0, 0
    for j, p in enumerate(P):
        numerical.append([p, 1])
        mixed = []
        for d, a in zip(D[1:], phases[j]):
            residue = a + d * ((-a * pow(d, -1, p)) % p)
            need(residue % d == a and residue % p == 0 and 0 <= residue < d * p,
                 'One CRT class per original numerical label')
            mixed.append((d * p, residue))
        numerical.extend(mixed)
        for x in rows:
            live = 0
            for t in range(p):
                point = x + 315 * (((t - x) * pow(315, -1, p)) % p)
                live += t != 1 and all(point % m != a for m, a in mixed)
                fibre_checks += 1
            need(live == p - 1 - (hits[x][j] > 0) and live >= lower[x][j],
                 'Actual distinct-root loss, not label hit count')
            strict_rows += live > lower[x][j]
    need(len(numerical) == len({m for m, _ in numerical}) == 71
         and all(m > 1 and m % 2 for m, _ in numerical), 'Distinct odd numerical originals')
    coeff = coefficients()
    joint, caps = joint_cost(rows, lower, weights)
    marginal, marginal_caps = marginal_cost(rows, lower, weights, coeff)
    uniform, _ = joint_cost(rows, lower, [1] * len(rows))
    product_weights = [prod(lower[x]) for x in rows]
    product_cost, _ = joint_cost(rows, lower, product_weights)
    need(uniform / 74 == F(122673875539055231, 91684362715545600) > 1,
         'Uniform rule fails this envelope')
    need(sum(product_weights) == 32297133
         and product_cost / sum(product_weights) == F(547112609, 516754128) > 1,
         'Product rule fails this envelope')
    need(joint / 102 == F(353776946866374881, 379127229607526400), 'Exact joint ratio')
    need(marginal / 102 == F(47292539850937617536238835637847876462092667791983,
                            49706518301412129989142768215521526478274560000000),
         'Exact single-axis ratio')
    need(joint <= marginal < F(119, 125) * 102, 'Strict common-source certificate')
    cap = max(F(w, prod(lower[x])) for x, w in zip(rows, weights))
    haar = (102 - marginal) / (315 * prod(P) * cap)
    # Finite checks of all required Newton degrees; never evaluate q-h at h>=q.
    newton_checks = 0
    for q in S:
        top = min(11, q - 1)
        for k in range(1, 6):
            delta = [sum(((-1) ** (m - t) * comb(m, t) * F(1, (q - t) ** k)
                          for t in range(m + 1)), F(0)) for m in range(top + 1)]
            need(all(c > 0 for c in delta), 'Positive truncated Newton coefficients')
            for h in range(top + 1):
                need(sum((comb(h, m) * delta[m] for m in range(h + 1)), F(0))
                     == F(1, (q - h) ** k), 'Finite Newton identity')
                newton_checks += 1
    return {
        'scope': 'Fixed core and five old singleton dictionaries; arbitrary outside roots, '
                 'shallow multioutside phases, finite core heights and larger ordered '
                 'outside primes. Outside exponents at most one. Not universal feasibility.',
        'input_sha256': sha256(raw).hexdigest(), 'core_rows': rows,
        'row_mass_pairs': list(map(list, zip(rows, weights))),
        'hit_histograms': [{str(h): sum(hits[x][j] == h for x in rows)
                            for h in sorted({hits[x][j] for x in rows})} for j in range(5)],
        'minimum_denominators': [min(lower[x][j] for x in rows) for j in range(5)],
        'actual_numerical_classes': numerical, 'actual_fibre_points_checked': fibre_checks,
        'rows_axes_with_strict_root_count_improvement': strict_rows,
        'scales': S, 'coefficients': [[str(coeff[j, k]) for k in range(1, 6)] for j in range(5)],
        'uniform_cost': uniform / 74, 'product_weight_mass': sum(product_weights),
        'product_weight_cost': product_cost / sum(product_weights), 'integer_mass': 102,
        'joint_cost': joint / 102, 'marginal_cost': marginal / 102,
        'marginal_margin': 102 - marginal, 'point_mass_cap': cap,
        'marginal_Haar_lower': haar, 'joint_caps': caps, 'marginal_caps': marginal_caps,
        'newton_domain_checks': newton_checks, 'lean_verification': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate(), default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    else:
        expected = json.loads(Path(__file__).with_suffix('.json').read_text())
        need(result == expected, 'Retained result matches exact recomputation')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('joint_caps', 'marginal_caps', 'actual_numerical_classes',
                                   'core_rows', 'row_mass_pairs')}, indent=2))
