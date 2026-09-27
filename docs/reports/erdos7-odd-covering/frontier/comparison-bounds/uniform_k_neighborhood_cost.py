#!/usr/bin/env python3
"""Source-uniform complete cost on a K neighborhood, with all heads and tails."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/uniform_k_neighborhood_cost.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/comparison-bounds/complete_off_face_cost.py': '0d53ac6dc99eac6db322525d94375c498e61cb1c5cacd8776327c70d311306c8',
    'frontier/source-budgets/shared_budget_affine_tail.py': 'bdf09dc45ec3f38d7791853c974d1fc637ce3da30cc78c155e643c9d66c60ebd',
    'frontier/source-budgets/actual_five_slot_source_modulus.py': '4dd89f4919d2150fa27ba405e586f6bfe74f76b6037b934441ca7ff5357afa86',
}
COORDINATES = ('E5-g*q5', 'E15-g*q15', 'E27', 'Ege4', 'E5deep', 'E15deep', 'omega')
PROBES = frozenset(((0, 1, 2, 0, 2, 1, 2), (1, 0, 0, 0, 0, 1, 1),
                    (1, 3, 4, 1, 2, 0, 3), (0, 2, 1, 1, 4, 4, 1)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def parameters(delta, rho):
    delta, rho = F(delta), F(rho)
    require(0 <= delta <= F(2, 27) and rho >= 0, 'Uniform nonnegative K rectangle')
    rbar = min(F(1, 520), 5*rho)
    h1 = F(1, 3)-delta/18
    v0 = min(F(1, 20), 3*delta/4+2*rbar)
    v1 = min(F(1, 10), 3*delta/4+rbar/h1)
    gap = min(F(1, 10)-rbar, h1/5-rbar, (F(1, 9)-delta/18)/5-rbar,
              h1*(F(1, 10)-3*delta/4)-2*rbar)
    require(gap > 0, 'Every actual wrong or absent shallow label has a positive uniform gap')
    return {'delta': delta, 'rho': rho, 'rbar': rbar, 'h1min': h1, 'v0': v0, 'v1': v1,
            'gap': gap, 'tbar': 2*(1+delta)/(1-4*delta),
            'Cbar': (F(3, 4)+delta/4)/(F(1, 5)-3*delta/8),
            'kbar': (6-delta)/(3-2*delta),
            'budget_increments': ((5*delta+delta**2)/72, delta/36, delta/4),
            'c': (F(7, 10)+delta/4, F(2, 5)+13*delta/90,
                  F(4, 15)+delta/15, F(4, 45)+delta/45),
            'H': (F(1, 20)+21*delta/20-delta**2/5,
                  F(1, 10)+(19*delta+2*delta**2)/90,
                  F(1, 15)+delta/9, F(1, 45)+delta/30-delta**2/360),
            'positive7': F(779, 12600)+367*delta/1260}


def enlarged_point(face_point, par):
    delta, v0, v1 = (par[k] for k in ('delta', 'v0', 'v1'))
    increments = []
    for i, cap in enumerate(face_point['caps']):
        c, j = divmod(i, 5)
        excluded = j == 0 or (j == 1 and c >= 2) or (j == 2 and c == 2)
        if excluded:
            increase = F(0)
            require(cap == 0, 'Exact original source exclusion')
        elif j != 3:
            increase = delta/90 if c == 0 else F(0)
        else:
            increase = delta/90+v0/18 if c == 0 else v0/9 if c == 1 else v1/9
        increments.append(increase)
    point = dict(face_point)
    point['score'] = (F(0),)+(1-delta,)*4
    point['caps'] = tuple(a+b for a, b in zip(face_point['caps'], increments))
    point['budgets'] = tuple(a+b for a, b in zip(face_point['budgets'], par['budget_increments']))
    return point, tuple(increments)


def selected_error(record, par):
    d, v = par['delta'], max(par['v0'], par['v1'])
    A = {k: sum((a for t, a in record['coefficients'].items() if record['prefix'][t] >= k), F(0))
         for k in range(1, 5)}
    return 13*d*A[1]/2250+A[2]*(v+d/5)/27+7*d*A[3]/2250+A[4]*(v+d/5)/81


def fixed_tail(affine, record, par, cuts):
    constant, slopes, details = F(0), [F(0)]*4, {}
    for t, a in record['coefficients'].items():
        details[t] = {}
        for j, (name, prime, start) in enumerate(zip(affine.FAMILIES, (3, 5, 5, 5), (3, 2, 2, 2))):
            support = affine.punctured_support(prime, start, affine.omissions(name, record['prefix'][t]), cuts[j])
            constant += a*(par['c'][j]*support['remaining_geometric']+par['H'][j]*support['intercept_coefficient'])
            slopes[j] += a*support['slope']
            details[t][name] = support
        constant += a*(F(1, 72)+par['positive7'])
    constant += slopes[1]*par['delta']/240
    return {'constant': constant, 'slopes': tuple(slopes), 'cuts': cuts, 'supports': details}


def mean_rows(mean, record, face, par):
    rows = []
    a1, kb = record['coefficients'].get(1, F(0)), par['kbar']
    for layout in mean.layouts():
        d = mean.mean_data(F(0), F(3, 4), F(1, 2), F(3, 4), face['dat'][2], face['qslots'], layout)
        I, J = int(layout[0] == 0), int(layout[3] == 0)
        L27 = d['joint_supremum']+max(d['wrong_cell_missing_supremum']*(par['Cbar']-1),
                                     d['full_root1_missing_supremum']*par['tbar'])
        Lge4 = d['Mxi']+I*(1+J)*par['tbar']
        prices = (8*a1/27, F(0), a1*L27, a1*Lge4,
                  a1*d['E5deep_price'], kb*a1*d['E15deep_price']/2, F(0))
        rows.append((layout, a1*d['reference'], prices))
    require(len(rows) == 12500, 'All original layouts')
    return tuple(rows)


def exhaustive_vertex(cost, finite, capacity, record, face, upper_point, par, rows, q):
    face_compiler = cost.IntegerHead(finite, record, face['point'], q)
    upper_compiler = cost.IntegerHead(finite, record, upper_point, q)
    residual = par['rho']-par['gap']*sum(q)
    require(residual >= 0, 'One common polygon vertex')
    mass_scale = lcm(face_compiler.scale, upper_compiler.scale)
    ffac, ufac = mass_scale//face_compiler.scale, mass_scale//upper_compiler.scale
    shifts = tuple((layout, tuple(-reference+residual*p for p in prices)) for layout, reference, prices in rows)
    scale = lcm(mass_scale, *(value.denominator for _, values in shifts for value in values))
    bfac = scale//mass_scale
    maxima, witnesses = [None]*7, [None]*7
    count, comparisons, digest = 0, 0, sha256()
    for layout, shift in shifts:
        B = face_compiler.load(layout)
        best, which = None, None
        for root, slot, extra in face_compiler.positive7:
            # Only the enlarged head LP is used; selected operators stay on the face.
            head = tuple(upper_compiler.head[i, extra[i], B[i]] for i in range(25))
            lp = sum(upper_compiler.capacity(head, group, budget)
                     for group, budget in zip(cost.GROUPS, upper_compiler.budgets))
            selected = 0
            for k, choices in enumerate(face_compiler.operators, 1):
                inc = tuple(face_compiler.inc[k, i, extra[i], B[i]] for i in range(25))
                selected += max(sum(weight*inc[i] for i, weight in row) for row in choices)
            value = ufac*lp+ffac*selected
            count += 1
            digest.update((str(value)+';').encode())
            if best is None or value > best:
                best, which = value, (root, slot)
            if layout in PROBES and (root, slot) == (0, 2):
                rational_head, _ = finite.finite_coefficients(record, upper_point, q, layout, (root, slot))
                expected_lp = sum(capacity.capacity_dual(rational_head, upper_point['caps'], budget, group)[0]
                                  for group, budget in zip(cost.GROUPS, upper_point['budgets']))
                face_branch = finite.branch(capacity, record, face['point'], q, layout, (root, slot))
                require(F(value, mass_scale) == expected_lp+sum(face_branch['selected']),
                        'Independent rational LP and selected operators agree')
                comparisons += 1
        for j, v in enumerate(shift):
            candidate = best*bfac+v.numerator*(scale//v.denominator)
            if maxima[j] is None or candidate > maxima[j]:
                maxima[j] = candidate
                witnesses[j] = {'layout': layout, 'positive7': which, 'finite_upper': F(best, mass_scale),
                                'reference_and_mean_price_shift': v}
    require(count == 125000 and comparisons == 4, 'All heads and independent rational checks')
    return {'q': q, 'residual': residual, 'head_maxima': tuple(F(n, scale) for n in maxima),
            'witnesses': witnesses, 'original_head_evaluations': count, 'rational_comparisons': comparisons,
            'integer_scale': scale, 'finite_objectives_sha256': digest.hexdigest()}


def apply_support(record, par, tail, vertices):
    P3, P5, P1, Pc = tail['slopes']
    prices = (P3, par['kbar']*P3, P5, P5, P3, par['kbar']*P3, record['M']+P3+P5+P1+Pc)
    a1 = record['coefficients'].get(1, F(0))
    constant = tail['constant']+selected_error(record, par)+a1*299*par['delta']/10800
    values = []
    for v in vertices:
        q, e = v['q'], v['residual']
        # The extra corrected mean price acts on E5-g*q5 only: no extra q shift.
        shifted = par['gap']*P3*(q[0]+par['kbar']*q[1])
        coordinates = tuple(constant+shifted+head+e*p for head, p in zip(v['head_maxima'], prices))
        values.append({'q': q, 'coordinate_values': coordinates, 'upper': max(coordinates)})
    upper = max(v['upper'] for v in values)
    return {'cuts': tail['cuts'], 'upper': upper, 'vertices': values, 'tail': tail,
            'selected_error': selected_error(record, par), 'mean_source_error': a1*299*par['delta']/10800}


def crossing(prime, start, H, epsilon):
    require(epsilon > 0, 'Positive radius gives a finite fixed complete-tail cut')
    cut = start
    while H*F(1, prime**cut) > epsilon:
        cut += 1
    return cut


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('uniform_k_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    cost = module('uniform_k_cost', base/'frontier/comparison-bounds/complete_off_face_cost.py')
    for path, pin in cost.PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned cost input '+path)
    finite = module('uniform_k_finite', base/'frontier/retained-transport/finite_source_face_transport.py')
    affine = module('uniform_k_affine', base/'frontier/source-budgets/shared_budget_affine_tail.py')
    mean = module('uniform_k_mean', base/'frontier/retained-transport/joint_deep_mean_transport.py')
    source = module('uniform_k_source', base/'verify_joint_frontier.py')
    capacity = module('uniform_k_capacity', base/'frontier/endpoint-bounds/broad_weighted_identity_source.py')
    old = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/whole_cost_mean_stop_loss.json'))
    row = old['cost_results'][1]
    require(row['index'] == 1 and row['name'] == 'R17' and row['tuple'] == [0, 1]
            and F(row['constant_mass_term']) == 0, 'One original cost with zero constant mass coefficient')
    record = finite.prepare({int(t): F(a) for t, a in row['objective']['coefficients'].items()})
    face = cost.face_case(finite, source)
    require(face['point']['budgets'] == (F(1, 36), F(1, 12), F(5, 36)), 'Whole beta-face grouped budgets')
    par = parameters(F(1, 10000), F(1, 100000))
    full = parameters(F(2, 27), F(1, 2600))
    require((full['tbar'], full['Cbar'], full['kbar'], full['gap']) ==
            (F(58, 19), F(415, 93), F(160, 77), F(6133, 568620)), 'Audited full-domain constants')
    upper_point, du = enlarged_point(face['point'], par)
    rows = mean_rows(mean, record, face, par)
    vertices = [exhaustive_vertex(cost, finite, capacity, record, face, upper_point, par, rows, q)
                for q in finite.defect_vertices(par['gap'], par['gap'], par['rho'])]
    eps = (par['kbar']*par['rho'], par['rho']+par['delta']/240, par['rho'], par['rho'])
    cuts = tuple(crossing(p, b, H, e) for p, b, H, e in zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], eps))
    candidates = sorted(set((cuts, (10, 10, 10, 10), (12, 12, 12, 12))))
    supports = [apply_support(record, par, fixed_tail(affine, record, par, cut), vertices) for cut in candidates]
    best = min(supports, key=lambda r: r['upper'])
    face_upper = F(row['uniform_cost_upper'])
    require(face_upper < best['upper'] < F(157, 100), 'A nonzero source-uniform rectangle below1.57')
    actual = cost.actual_398_case(finite, source, 12)
    require(actual['sigma'] <= par['delta'] and actual['defects']['rho'] <= par['rho']
            and actual['point']['r'] <= par['rbar'], 'One genuine finite source is inside the certified rectangle')
    require(all(a <= b for a, b in zip(actual['point']['caps'], upper_point['caps']))
            and all(a <= b for a, b in zip(actual['point']['budgets'], upper_point['budgets']))
            and all(a >= b for a, b in zip(actual['point']['score'], upper_point['score'])),
            'Genuine source confirms cap, group and coefficient domination')
    require(actual['defects']['E5']-par['gap']*actual['q'][0] >= actual['point']['r']/5,
            'The corrected first residual price needs no extra q shift')
    return encode({'schema': 'erdos7-uniform-k-neighborhood-cost-v1', 'source_sha256': {**PINS, **cost.PINS},
                   'cost_index': 1, 'cost_name': 'R17', 'cost_tuple': (0, 1), 'parameters': par,
                   'capacity_increments': du, 'uniform_caps': upper_point['caps'],
                   'uniform_budgets': upper_point['budgets'], 'uniform_score_lower': upper_point['score'],
                   'coordinates': COORDINATES, 'exhaustive_vertices': vertices, 'cut_candidates': supports,
                   'selected_support': best, 'uniform_complete_upper': best['upper'],
                   'face_complete_upper': face_upper, 'uniform_excess': best['upper']-face_upper,
                   'upper_rational_comparison': F(157, 100), 'margin_below_comparison': F(157, 100)-best['upper'],
                   'actual_finite_example': {'height': 12, 'sigma': actual['sigma'], 'rho': actual['defects']['rho'],
                                            'r': actual['point']['r'], 'q': actual['q']},
                   'full_radius_checked_constants': full,
                   'original_head_evaluations': sum(v['original_head_evaluations'] for v in vertices),
                   'rational_comparisons': sum(v['rational_comparisons'] for v in vertices),
                   'scope': 'Ordinary continuum theorem plus exhaustive exact arithmetic for one original complete AP cost, uniformly over actual concentrated sources with sigma<=1/10000, rho<=1/100000 and r<=1/520. Both K orientations and every feasible beta distribution are included by group domination and relabeling; all original heads, common q polygon, seven residual coordinates and infinite exponent tails are retained. No global K improvement, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('uniform_k_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact uniform neighborhood certificate')
    print('PASS: uniform complete cost '+result['uniform_complete_upper'])
    print('All original heads, common polygon, seven residual coordinates and complete infinite tails retained.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
