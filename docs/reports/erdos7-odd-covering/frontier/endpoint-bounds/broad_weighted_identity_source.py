#!/usr/bin/env python3
"""Pointwise weighted identity-source upper bounds on the broad actual slab.

The ordinary proof supplies arbitrary-source validity. Every evaluated head
uses exact rational capacity duals, independently checked against a primal.
The retained direction probes do not assert a uniform positive slab gain.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/broad_weighted_identity_source.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'verify_joint_frontier.py': '85341d7f8fa2d0b109697bc17b005a7e75f7f6ec412fd2eb3d26383cf9fce24f',
    'frontier/endpoint-bounds/endpoint_linear_neighborhood.py': '1c8ccd9850a12019081181f53440606583bcd9781fd9949a30cd2d8e5a2503b3',
    'frontier/endpoint-bounds/broad_five_slot_tradeoff.py': '73a23d45c240ac9cd59216243127030e86f188d7dca930f689c44437799c59c5',
    'certificates/source_norms/endpoint-bounds/broad_five_slot_tradeoff.json': '563dd67bdd067108b08c0f9290d55271104559c1b01af7ba97cb61f97a6dc15c',
    'frontier/endpoint-bounds/broad_clipped_identity.py': 'c52206107738e36de54434e8d7419a557387c52d57d92c4d59186226dd01d169',
    'certificates/source_norms/endpoint-bounds/broad_clipped_identity.json': '984a6014b2322d867cc2b2f69b649321a7f4b3651821619763644d03dcac2494',
}
ROOT = (0, 0, 1, 1, 1)
CARRIERS = tuple(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4)))
PARTITIONS = {
    'three_groups': (tuple(range(5)), tuple(range(5, 10)), tuple(range(10, 25))),
    'five_rows': tuple(tuple(range(5*c, 5*c+5)) for c in range(5)),
}
LAYOUTS = tuple(product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)))
HEADS = tuple(tuple(1+int(ROOT[c] == r3)+int(c == c9)+int(s == s5)
                   +int(ROOT[c] == r15 and s == s15)+int(c == c45 and s == s45)
                   for c, s in product(range(5), repeat=2))
              for r3, c9, s5, r15, s15, c45, s45 in LAYOUTS)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def carrier_score(pi):
    require(all(isinstance(value, (int, F)) for value in pi), 'Exact rational carrier weights')
    require(len(pi) == 18 and min(pi) >= 0 and sum(pi) == 1, 'One actual common-carrier probability vector')
    return tuple(sum(weight*(int(ROOT[c] == root)+int(c == cell))
                     for weight, (root, cell) in zip(pi, CARRIERS)) for c in range(5))


def point_carrier(root, cell):
    return tuple(F(int(c == (root, cell))) for c in CARRIERS)


def capacity_dual(coefficients, capacities, budget, indices):
    """Exact minimum over gamma=0 or a coefficient; check primal equality."""
    require(budget >= 0 and all(coefficients[i] >= 0 and capacities[i] >= 0 for i in indices), 'Capacity problem domain')
    remaining, gamma = budget, F(0)
    allocation = {i: F(0) for i in indices}
    for i in sorted(indices, key=lambda i: (-coefficients[i], i)):
        take = min(capacities[i], remaining)
        allocation[i] = take
        remaining -= take
        if take:
            gamma = coefficients[i]
        if remaining == 0:
            break
    if remaining:
        gamma = F(0)
    if budget == 0:
        gamma = max((coefficients[i] for i in indices), default=F(0))
    alpha = {i: max(coefficients[i]-gamma, F(0)) for i in indices}
    require(gamma >= 0 and all(gamma+alpha[i] >= coefficients[i] for i in indices), 'Feasible capacity dual')
    require(all(0 <= allocation[i] <= capacities[i] for i in indices)
            and sum(allocation.values()) <= budget, 'Feasible capacity primal')
    primal = sum(coefficients[i]*allocation[i] for i in indices)
    dual = gamma*budget+sum(capacities[i]*alpha[i] for i in indices)
    require(primal == dual, 'Exact independently checked capacity optimum')
    return dual, gamma


def source_tables(parameter, dat, score, r, first_beta):
    deficit, alpha, beta, late, z = parameter
    d, n, eta, s, _ = dat
    require(first_beta in (2, 3, 4), 'Actual first-beta source cell')
    require(0 <= r < F(1, 12000), 'Small-best-slot-loss branch')
    Delta = z-F(3, 4)+F(1, 4)-alpha[1]+F(1, 4)-sum(beta[2:])
    require(F(0) <= Delta <= F(1, 18), 'Broad actual source slab')
    require(min(deficit+alpha+beta+late) >= 0 and sum(deficit) <= F(1, 2)
            and sum(alpha) <= F(1, 4) and sum(beta) <= F(1, 4)
            and sum(late) <= F(1, 72) and F(3, 4) <= z <= 1, 'Actual source parameter domain')
    h, h1 = sum(eta), sum(eta[2:])
    a = tuple(1-v/5 for v in score)
    b = (1, 1, 2, 2, 2)
    w = tuple(a[c]-F(b[c]*int(slot == 4), 5) for c, slot in product(range(5), repeat=2))
    require(min(w) >= F(1, 5), 'Nonnegative retained density')
    pre = []
    for c, slot in product(range(5), repeat=2):
        excluded = slot == 0 or (slot == 1 and c >= 2) or (slot == 2 and c == first_beta)
        value = F(0) if excluded else F(1, 5)
        if slot == 3:
            value = min(value, F(3, 20)+Delta+r/h if c < 2 else F(1, 10)+Delta+r/h1)
        pre.append(value)
    caps = tuple(eta[c]*pre[5*c+slot] for c, slot in product(range(5), repeat=2))
    failures = []
    for c in range(5):
        if n[c] < eta[c]/5-r:
            failures.append('row'+str(c)+': n_c<eta_c/5-r')
        if n[c] > sum(caps[5*c:5*c+5]):
            failures.append('row'+str(c)+': n_c exceeds its complete slot-cap sum')
    if s < h/5-r:
        failures.append('total source mass is below the actual H mass')
    for name, groups in PARTITIONS.items():
        for number, group in enumerate(groups):
            cells = sorted({i//5 for i in group})
            if sum(n[c]-eta[c]/5 for c in cells)+r < 0:
                failures.append(name+str(number)+': non-H mass upper is negative')
    return {'Delta': Delta, 'r': r, 'first_beta': first_beta, 'a': a, 'b': b,
            'weights': w, 'pre_coefficients': tuple(pre), 'capacities': caps,
            'necessary_condition_failures': failures}


def source_head(caps, n, w, r):
    """All original shallow tests; two partitions with/without H mass."""
    budgets = {name: tuple(sum(n[c] for c in sorted({i//5 for i in group})) for group in groups)
               for name, groups in PARTITIONS.items()}
    maxima = {name+suffix: None for name in PARTITIONS for suffix in ('', '_H')}
    best, witness, digest = None, None, sha256()
    for layout, B in zip(LAYOUTS, HEADS):
        coefficients = tuple(weight*value for weight, value in zip(w, B))
        values, duals = {}, {}
        for name, groups in PARTITIONS.items():
            plain, kept, gammas = F(0), F(0), []
            for group, budget in zip(groups, budgets[name]):
                value, gamma = capacity_dual(coefficients, caps, budget, group)
                plain += value
                H = tuple(i for i in group if i % 5 == 4)
                rest = tuple(i for i in group if i % 5 != 4)
                residual = budget-sum(caps[i] for i in H)+r
                require(residual >= 0, 'Actual H group mass feasibility')
                value_H, gamma_H = capacity_dual(coefficients, caps, residual, rest)
                kept += sum(coefficients[i]*caps[i] for i in H)+value_H
                gammas.append((gamma, gamma_H))
            values[name], values[name+'_H'], duals[name] = plain, kept, gammas
        value = min(values.values())
        for name, candidate in values.items():
            maxima[name] = candidate if maxima[name] is None else max(maxima[name], candidate)
        digest.update(json.dumps(encode([layout, values, duals]), separators=(',', ':')).encode())
        if best is None or value > best:
            best = value
            witness = {'layout': layout, 'method_values': values, 'dual_gammas': duals}
    return {'upper': best, 'head_count': len(LAYOUTS), 'method_uppers': maxima,
            'all_heads_and_duals_sha256': digest.hexdigest(), 'maximizing_witness': witness}


def old_source_lower(source, old, dat, score):
    """Same pi throughout: every fixed old layout upper-bounds its margin."""
    d, n, eta, s, _ = dat
    rest = (max(d)/18+(sum(eta)+max(sum(eta[:2]), sum(eta[2:]))+max(eta))/4+F(1, 72))/5
    S0 = s-rest-sum(weight*mass for weight, mass in zip(score, n))/5
    candidates = []
    for b0, c0 in product(source.BASES, repeat=2):
        k = tuple(F(6-v) for v in b0)
        A = tuple(k[j]*n[j]-c0[j]*eta[j]/5 for j in range(5))
        z = tuple(k[j]*d[j]-F(c0[j], 5) for j in range(5))
        width = tuple(9*eta[j]*k[j] for j in range(5))
        T = F(13, 243)*max(z)+F(1, 486)*max(k[j]*d[j] for j in range(5))
        T += (sum(width)+max(sum(width[:2]), sum(width[2:]))+max(width))/36+max(k)/72
        U = old.exact_old_U(dat, b0, c0, source.BASES)
        lower = 6*S0-6*s+U+(sum(weight*x for weight, x in zip(score, A))+T)/5
        candidates.append((lower, b0, c0))
    value, b0, c0 = max(candidates)
    return {'S0': S0, 'lower': value, 'old_fixed_layout': (b0, c0), 'fixed_layout_count': len(candidates)}


def bound(source, old, parameter, pi, r=F(0), first_beta=2):
    dat = source.data(parameter)
    d, n, eta, s, _ = dat
    score = carrier_score(pi)
    table = source_tables(parameter, dat, score, r, first_beta)
    record = {'parameter': parameter, 'pi': pi, 'carrier_score': score, 'table': table}
    if table['necessary_condition_failures']:
        record['scope'] = 'Excluded by necessary actual-source conditions for this first-beta cell and r; not an actual-source counterexample.'
        return record
    w, a, b = table['weights'], table['a'], table['b']
    head = source_head(table['capacities'], n, w, r)
    descendant = tuple(F(0) if table['pre_coefficients'][5*c+j] == 0 else eta[c]*w[5*c+j]
                       for c, j in product(range(5), repeat=2))
    pure3 = max(a[c]*d[c]-F(b[c], 25) for c in range(5))/18+F(2, 5)*r
    require(min(a[c]*d[c]-F(b[c], 25) for c in range(5)) >= 0, 'Positive deep3 uniform coefficients')
    positive5 = (max(sum(descendant[5*c+j] for c in range(5)) for j in range(5))
                 +max(sum(descendant[5*c+j] for c in range(5) if ROOT[c] == root)
                      for root, j in product(range(2), range(5)))+max(descendant))/20
    tails = {'pure3': pure3, 'descendant5': positive5, 'deep35': F(1, 72)}
    positive7 = (s+old.complete_cap(dat))/5
    upper = head['upper']+sum(tails.values())+positive7
    previous = old_source_lower(source, old, dat, score)
    record.update({'head': head, 'complete_tails': tails, 'positive7': positive7,
                   'source_upper': upper, 'old_comparison': previous,
                   'source_gain': previous['lower']-upper})
    return record


def cases(source):
    base = list(source.vertices())[398]
    pi = point_carrier(1, 1)
    result = []
    for coordinate in ('p', 'a', 'b'):
        for amount in (F(1, 1000), F(1, 100), F(1, 18)):
            par = [list(v) if isinstance(v, tuple) else v for v in base]
            if coordinate == 'p':
                par[4] += amount
            if coordinate == 'a':
                par[1][1] -= amount
            if coordinate == 'b':
                par[2][2] -= amount
            result.append((coordinate+'='+str(amount), tuple(tuple(v) if isinstance(v, list) else v for v in par), pi, F(0)))
    for location in range(5):
        par = list(base)
        par[3] = tuple(F(1, 72) if j == location else F(0) for j in range(5))
        result.append(('late'+str(location), tuple(par), pi, F(0)))
    for location in range(-1, 5):
        par = list(base)
        par[0] = tuple(F(1, 2) if j == location else F(0) for j in range(5))
        result.append(('deficit'+str(location), tuple(par), pi, F(0)))
    for root, cell in CARRIERS:
        result.append(('carrier'+str((root, cell)), base, point_carrier(root, cell), F(0)))
    result.append(('positive_r', base, pi, F(1, 24000)))
    result.append(('p=1/20', base[:4]+(F(4, 5),), pi, F(0)))
    mixed = tuple((x+y)/2 for x, y in zip(pi, point_carrier(-1, 2)))
    result.append(('mixed_pi', base, mixed, F(0)))
    return result


def face_branch_checks(source, old):
    """Constant branches on the entire beta simplex; no optimized-value interpolation."""
    base = list(source.vertices())[398]
    eta = source.data(base)[2]
    b0, c0 = (2, 3, 1, 1, 1), (1, 2, 2, 2, 2)
    score = carrier_score(point_carrier(1, 1))
    k = (F(4), F(3), F(5), F(5), F(5))
    beta_samples = [(F(1, 4), F(0), F(0)), (F(0), F(1, 4), F(0)),
                    (F(0), F(0), F(1, 4)), (F(1, 12),)*3, (F(1, 5), F(1, 40), F(1, 40))]
    records = []
    for beta in beta_samples:
        parameter = base[:2]+((F(0), F(0))+beta,)+base[3:]
        dat = source.data(parameter)
        d, n, _, s, D = dat
        require(all(F(1, 4) <= v <= F(1, 2) for v in d[2:]) and sum(d[2:]) == F(5, 4), 'Whole-face density range and sum')
        require(s == F(1, 4) and D == F(53, 360) and max(d) == F(3, 4)
                and max(n) == F(1, 12) and max(sum(n[:2]), sum(n[2:])) == F(5, 36), 'Fixed complete-cap branches')
        z = tuple(k[l]*d[l]-F(c0[l], 5) for l in range(5))
        require(max(z) == z[0] == F(14, 5) and max(k[l]*d[l] for l in range(5)) == 3, 'Fixed old deep branches, controlled by cell0')
        weighted3 = tuple((1-score[l]/5)*d[l]-F(1+int(l >= 2), 25) for l in range(5))
        require(max(weighted3) == weighted3[0] == F(71, 100), 'Weighted deep3 face branch')
        A = tuple(k[l]*n[l]-c0[l]*eta[l]/5 for l in range(5))
        require(sum(score[l]*A[l] for l in range(5)) == F(23, 30), 'Constant old carrier term on whole beta simplex')
        U = old.exact_old_U(dat, b0, c0, source.BASES)
        require(U == F(8, 9) and old.complete_cap(dat) == F(37, 72), 'Constant old U and raw positive-seven cap')
        records.append({'beta': beta, 'density': d, 'old_U': U, 'old_z': z})
    table = source_tables(base, source.data(base), score, F(0), 2)
    for first in (2, 3, 4):
        moved = source_tables(base, source.data(base), score, F(0), first)
        swap = list(range(5))
        swap[2], swap[first] = swap[first], swap[2]
        require(all(table['capacities'][5*l+j] == moved['capacities'][5*swap[l]+j]
                    and table['weights'][5*l+j] == moved['weights'][5*swap[l]+j]
                    for l, j in product(range(5), repeat=2)), 'First-beta cell symmetry preserves the weighted capacity table')
    T = F(13, 243)*F(14, 5)+F(1, 486)*3+F(40, 36)+F(5, 72)
    require(T == F(12991, 9720)
            and 6*F(53, 360)-6*F(1, 4)+F(8, 9)+(F(23, 30)+T)/5 == F(33673, 48600),
            'Uniform old fixed-layout comparison')
    return {'density_interval_root1': [F(1, 4), F(1, 2)], 'density_sum_root1': F(5, 4),
            'group_masses': [F(1, 36), F(1, 12), F(5, 36)],
            'non_H_group_masses': [F(1, 60), F(11, 180), F(13, 180)],
            'old_layout': [b0, c0], 'old_T': T, 'old_carrier': F(23, 30),
            'branch_checks': records,
            'justification': 'The ordinary proof uses these fixed max branches and fixed group masses on the full beta simplex. The exact samples check the formulas, not a claimed interpolation of optimized LP values.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('weighted_source_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source: '+path)
    clipped = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/endpoint-bounds/broad_clipped_identity.json'))
    source = module('weighted_source_parent', base/'verify_joint_frontier.py')
    old = module('weighted_source_old', base/'frontier/endpoint-bounds/endpoint_linear_neighborhood.py')
    require(capacity_dual((F(3), F(1)), (F(1), F(1)), F(0), (0, 1)) == (F(0), F(3)),
            'Zero non-H source budget keeps an exact feasible dual')
    records = {}
    for name, parameter, pi, r in cases(source):
        records[name] = bound(source, old, parameter, pi, r)
    face = records['late0']
    require(face['head']['upper'] == face['head']['method_uppers']['three_groups_H'] == F(11, 25),
            'The fixed three-group H method gives the whole-face head bound')
    require(face['head']['method_uppers']['three_groups'] == F(67, 150)
            and sum(face['complete_tails'].values()) == F(11, 120), 'Old weak head and complete tail independently recovered')
    require(face['source_upper'] == F(154, 225) and face['old_comparison']['lower'] == F(33673, 48600)
            and face['source_gain'] == F(409, 48600), 'Whole-face source comparison anchor')
    require(records['p=1/20']['source_gain'] == F(137, 24300)
            and records['a=1/18']['source_gain'] == F(157, 48600)
            and records['b=1/18']['source_gain'] == F(187, 48600), 'Three boundary direction probes')
    require(records['p=1/18']['table']['necessary_condition_failures'], 'Forced source5 excludes the z>4/5 relaxed input')
    require(records['deficit2']['source_gain'] == -F(779, 48600)
            and records['deficit3']['source_gain'] == records['deficit4']['source_gain'] == -F(347, 48600),
            'Negative deficit-direction comparisons are retained')
    require(records['carrier(-1, 2)']['source_gain'] == records['carrier(1, 2)']['source_gain'] == -F(23, 48600),
            'Negative carrier-direction comparisons are retained')
    require(records['late2']['table']['necessary_condition_failures'], 'The impossible small-r row is reported explicitly')
    tail = F(clipped['complete_clipped_tail'])
    coefficient = F(clipped['common_deficiency_coefficient'])
    for record in records.values():
        if 'source_gain' in record:
            record['gain_after_complete_clipped_tail'] = record['source_gain']-tail
    return {'schema': 'erdos7-broad-weighted-identity-source-v1', 'source_sha256': used,
            'canonical_slots': {'P': 0, 'A': 1, 'B': 2, 'Q': 3, 'H': 4},
            'complete_clipped_tail': tail, 'shared_deficiency_coefficient': coefficient,
            'comparison_formula': 'new_margin-old_m40 >= source_gain-T40+(6-c)*rho+c*(r+r1)/5; use the positive part when combining with the old valid margin.',
            'whole_face_fixed_branches': face_branch_checks(source, old),
            'pointwise_records': records, 'record_count': len(records),
            'scope': 'Ordinary actual-source pointwise theorem on the complete small-r slab, with exact finite dual evaluation. Direction probes are not a uniform slab optimization, actual-covering constructions, global K improvement, or Lean verification. The ordinary proof supplies whole-face continuation by fixed group masses, not by interpolation of new LP values.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('weighted_source_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical weighted-source certificate')
    elif args.write or args.output is not None:
        io.write_certificate_text(args.output or args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: exact pointwise source duals, complete tails,409/48600 face anchor and retained negative directions. No uniform positive slab gain claimed.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
