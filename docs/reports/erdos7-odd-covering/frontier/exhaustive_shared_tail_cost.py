#!/usr/bin/env python3
"""Exhaustive fixed-source cost with complete tails and a common defect budget."""
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
CERTIFICATE = 'certificates/source_norms/exhaustive_shared_tail_cost.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/shared_budget_affine_tail.py': '0b0a509626dda7f44ecccf56825c2a3027fce2e4269c64a0419e65da3bce1136',
    'certificates/source_norms/complete_off_face_cost.json': '6b8555e55c2348cb5725f45b6a4cc771e9cd8e738d6c48bbfc4c0eab6e26b763',
}
MEAN_PRICES = ('E27_price', 'Ege4_price', 'E5deep_price', 'E15deep_price')
COORDINATE_MAP = (0, 0, 1, 2, 3, 4, 0)
PROBES = frozenset(((0, 1, 2, 0, 2, 1, 2), (1, 0, 0, 0, 0, 1, 1),
                    (1, 3, 4, 1, 2, 0, 3), (0, 2, 1, 1, 4, 4, 1)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable exact input')
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


def source_gaps(case):
    caps, eta = case['point']['caps'], case['dat'][2]
    h, h1 = sum(eta), sum(eta[2:])
    require(case['point']['r'] == case['point']['r1'] == 0, 'Actual398 source has a full source-free H slot')
    g5 = h/5-max(sum(caps[5*l+j] for l in range(5)) for j in range(4))
    g15 = h1/5-max(max(sum(caps[5*l+j] for l in range(2, 5)) for j in range(4)),
                     max(sum(caps[5*l+j] for l in range(2)) for j in range(5)))
    require(g5 > 0 and g15 > 0, 'Actual cap table bounds every wrong or absent shallow carrier')
    return g5, g15


def prepare_mean_heads(mean, record, case):
    d, _, eta, _, _ = case['dat']
    a1 = record['coefficients'].get(1, F(0))
    rows, denominators = [], set()
    for layout in mean.layouts():
        data = mean.mean_data(case['sigma'], max(d), max(d[2:]), case['parameter'][4], eta, case['qslots'], layout)
        values = (a1*(data['reference']-data['source_error']),)+tuple(a1*data[k] for k in MEAN_PRICES)
        require(min(values[1:]) >= 0, 'Nonnegative same-head defect prices')
        denominators.update(v.denominator for v in values)
        rows.append((layout, values))
    scale = lcm(*denominators)
    require(len(rows) == 12500, 'Every original six-label layout appears once')
    return scale, tuple((layout, tuple(int(scale*v) for v in values)) for layout, values in rows)


def exhaustive_coordinate_heads(cost, finite, record, case, mean_scale, rows, q, g5, g15):
    """Five head maxima suffice for all seven residual coordinates and all cuts."""
    e = case['defects']['rho']-g5*q[0]-g15*q[1]
    require(e >= 0, 'One feasible shared packing vertex')
    compiler = cost.IntegerHead(finite, record, case['point'], q)
    scale = lcm(compiler.scale, e.denominator*mean_scale)
    raw_factor, ref_factor = scale//compiler.scale, scale//mean_scale
    price_factor = e.numerator*(scale//(e.denominator*mean_scale))
    maxima, witnesses, ties = [None]*5, [None]*5, [0]*5
    digest, original_count, probe_checks = sha256(), 0, 0
    for layout, values in rows:
        B = compiler.load(layout)
        best, best_seven = None, None
        for r, j, extra in compiler.positive7:
            value = compiler.branch(B, extra)
            digest.update((str(value)+';').encode())
            original_count += 1
            if best is None or value > best:
                best, best_seven = value, (r, j)
        base = raw_factor*best-ref_factor*values[0]
        candidates = (base,)+tuple(base+price_factor*p for p in values[1:])
        if layout in PROBES:
            expected_base = F(best, compiler.scale)-F(values[0], mean_scale)
            expected = (expected_base,)+tuple(expected_base+e*F(p, mean_scale) for p in values[1:])
            require(tuple(F(n, scale) for n in candidates) == expected, 'Integer and rational same-head coordinate objectives agree')
            probe_checks += len(candidates)
        for j, candidate in enumerate(candidates):
            if maxima[j] is None or candidate > maxima[j]:
                maxima[j] = candidate
                witnesses[j] = {'layout': layout, 'positive7': best_seven,
                                'finite_upper': F(best, compiler.scale),
                                'reference_payment': F(values[0], mean_scale),
                                'mean_price_payment': F(0) if j == 0 else F(values[j], mean_scale)}
                ties[j] = 1
            elif candidate == maxima[j]:
                ties[j] += 1
    require(original_count == 125000 and probe_checks == 20, 'All original heads and independent positive-seven pairs retained')
    return {'q': q, 'residual': e, 'head_maxima': tuple(F(maxima[j], scale) for j in COORDINATE_MAP),
            'witnesses': tuple(witnesses[j] for j in COORDINATE_MAP),
            'maximizing_layout_counts': tuple(ties[j] for j in COORDINATE_MAP),
            'integer_head_scale': compiler.scale, 'joint_scale': scale,
            'original_head_evaluations': original_count, 'coordinate_fraction_checks': probe_checks,
            'all_original_finite_objectives_sha256': digest.hexdigest()}


def crossing(prime, start, H, e):
    if e == 0:
        return max(10, start)
    cut = start
    while H*F(1, prime**cut) > e:
        cut += 1
    return cut


def support_candidates(affine, tail, record, case):
    parameters = affine.tail_affine(tail, record, dict(zip(affine.FAMILIES, (3, 2, 2, 2))))['family_parameters']
    rho, kappa = case['defects']['rho'], tail['root_wrong_price']
    maximum_errors = (kappa*rho, rho+(tail['z']-tail['family_parameters']['pure3']['raw'])/90, rho, rho)
    center = tuple(crossing(row['prime'], row['start'], row['H'], e)
                   for row, e in zip((parameters[name] for name in affine.FAMILIES), maximum_errors))
    choices = set(product(*(tuple(sorted({max(parameters[name]['start'], cut+d) for d in (-1, 0, 1)}))
                            for name, cut in zip(affine.FAMILIES, center))))
    choices.add(tuple(tail['complete_series'][0][name]['crossing'] for name in affine.FAMILIES))
    for common in (10, 12, 16):
        choices.add((common,)*4)
    return center, tuple(dict(zip(affine.FAMILIES, cuts)) for cuts in sorted(choices))


def evaluate_fixed_support(affine, tail, record, case, a0, g5, g15, vertices, cuts):
    envelope = affine.tail_affine(tail, record, cuts)
    p = envelope['defect_prices']
    base_prices = (p['E5'], p['E15'], p['E3'], p['E3'], p['E5d'], p['E15d'], p['omega']+record['M'])
    vertex_values = []
    for vertex in vertices:
        q, e = vertex['q'], vertex['residual']
        constant = a0*case['survivor_mass']+envelope['constant']+p['E5']*g5*q[0]+p['E15']*g15*q[1]
        coordinates = tuple(constant+H+e*price for H, price in zip(vertex['head_maxima'], base_prices))
        vertex_values.append({'q': q, 'coordinate_values': coordinates, 'upper': max(coordinates)})
    maximum = max(v['upper'] for v in vertex_values)
    return {'cuts': dict(cuts), 'upper': maximum, 'vertices': vertex_values,
            'maximizing_vertices': tuple(i for i, v in enumerate(vertex_values) if v['upper'] == maximum),
            'tail_constant': envelope['constant'], 'tail_defect_prices': p}


def omega_relaxation_lower(affine, tails, tail, record, case, a0, vertices):
    """An exact feasible relaxed objective, independent of the cut candidate set.

    This is a lower bound on every attainable relaxation upper, not on
    the actual covering cost. The all-omega allocation need not be realizable.
    """
    zero = next(vertex for vertex in vertices if vertex['q'] == (F(0), F(0)))
    rho = case['defects']['rho']
    parameters = affine.tail_affine(tail, record, dict(zip(affine.FAMILIES, (3, 2, 2, 2))))['family_parameters']
    errors = dict(zip(affine.FAMILIES,
                     (rho, rho+(tail['z']-tail['family_parameters']['pure3']['raw'])/90, rho, rho)))
    total, crossings, details = F(0), {}, {}
    for t, a in record['coefficients'].items():
        rows = {}
        for name, row in parameters.items():
            result = tails.complete_series(((row['c'], errors[name], row['H']),), row['c']+row['H'],
                                            row['prime'], row['start'], affine.omissions(name, record['prefix'][t]))
            rows[name] = result
            crossings[name] = result['crossing']
        total += a*(sum(row['upper'] for row in rows.values())+tail['raw_deep_mixed']+tail['positive7'])
        details[t] = rows
    lower = a0*case['survivor_mass']+zero['head_maxima'][0]+record['M']*rho+total
    finite_attainment = all(errors[name] > 0 or row['H'] == 0 for name, row in parameters.items())
    return {'relaxation_lower': lower, 'exact_complete_tail': total, 'family_errors': errors,
            'complete_series': details, 'attaining_cuts': crossings if finite_attainment else None,
            'allocation': (F(0),)*6+(rho,), 'q': (F(0), F(0)),
            'scope': 'Feasible relaxed envelope value; no actual-family realization or actual-cost lower bound.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('exhaustive_tail_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    affine = module('exhaustive_tail_affine', base/'frontier/shared_budget_affine_tail.py')
    for path, pin in affine.PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned affine input '+path)
    cost = module('exhaustive_tail_cost', base/'frontier/complete_off_face_cost.py')
    for path, pin in cost.PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned actual-cost input '+path)
    finite = module('exhaustive_tail_finite', base/'frontier/finite_source_face_transport.py')
    mean = module('exhaustive_tail_mean', base/'frontier/joint_deep_mean_transport.py')
    tails = module('exhaustive_tail_complete', base/'frontier/complete_off_face_omitted_tails.py')
    source = module('exhaustive_tail_source', base/'verify_joint_frontier.py')
    old = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/whole_cost_mean_stop_loss.json'))
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/complete_off_face_cost.json'))
    row = old['cost_results'][1]
    require(row['index'] == 1 and row['name'] == 'R17' and row['tuple'] == [0, 1], 'One existing complete original AP cost')
    record = finite.prepare({int(t): F(a) for t, a in row['objective']['coefficients'].items()})
    a0 = F(row['constant_mass_term'])
    results = []
    for case, prior in zip([cost.face_case(finite, source)]+[cost.actual_398_case(finite, source, h) for h in (5, 8)], previous['cost_results']):
        require(case['height'] == prior['source_height'], 'Exact source-by-source126 comparison')
        g5, g15 = source_gaps(case)
        require(g5 == g15 == F(1, 45), 'Measured actual-source packing prices')
        qvertices = finite.defect_vertices(g5, g15, case['defects']['rho'])
        mean_scale, heads = prepare_mean_heads(mean, record, case)
        vertices = [exhaustive_coordinate_heads(cost, finite, record, case, mean_scale, heads, q, g5, g15) for q in qvertices]
        tail = tails.complete_tails(case['dat'], case['pi'], case['defects'], case['parameter'][4])
        center, candidates = support_candidates(affine, tail, record, case)
        supports = [evaluate_fixed_support(affine, tail, record, case, a0, g5, g15, vertices, cuts) for cuts in candidates]
        upper = min(support['upper'] for support in supports)
        best = next(support for support in supports if support['upper'] == upper)
        prior_upper = F(prior['complete_cost_upper'])
        require(upper >= prior_upper, 'The whole-budget support relaxation dominates the computed actual-defect126 cost')
        v_index = best['maximizing_vertices'][0]
        vertex = vertices[v_index]
        coord = next(j for j, value in enumerate(best['vertices'][v_index]['coordinate_values']) if value == upper)
        witness = vertex['witnesses'][coord]
        d, _, eta, _, _ = case['dat']
        m = mean.mean_data(case['sigma'], max(d), max(d[2:]), case['parameter'][4], eta, case['qslots'], witness['layout'])
        envelope = affine.tail_affine(tail, record, best['cuts'])
        branch = affine.branch_affine(envelope, record, m, F(0), F(0), g5, g15, case['defects']['rho'], a0, case['survivor_mass'])
        require(affine.evaluate_branch(branch, witness['finite_upper'], vertex['q']) == upper,
                'Global support witness is exactly the same127 original-head branch')
        original_tail = sum(a*(tail['old_remainders'][record['prefix'][t]]+tail['positive7']) for t, a in record['coefficients'].items())
        chosen_actual_tail = affine.evaluate_tail(envelope, case['defects'])
        lower = omega_relaxation_lower(affine, tails, tail, record, case, a0, vertices)
        if case['height'] is None:
            require(upper-prior_upper == chosen_actual_tail-original_tail and upper > prior_upper,
                    'The finite-cut face excess is exactly its retained complete geometric intercept')
            require(lower['relaxation_lower'] == prior_upper and lower['attaining_cuts'] is None,
                    'The face all-support infimum is exact but no finite-cut support attains it')
        else:
            require(lower['relaxation_lower'] == upper and lower['attaining_cuts'] == best['cuts'],
                    'Independent complete-series lower matches the entire polygon upper: optimal over all cuts and convex mixtures')
        results.append({'height': case['height'], 'cost_index': row['index'], 'cost_tuple': row['tuple'],
                        'g5': g5, 'g15': g15, 'rho': case['defects']['rho'], 'survivor_mass': case['survivor_mass'],
                        'mean_scale': mean_scale, 'exhaustive_vertices': vertices,
                        'support_center_from_full_budget': center, 'support_candidates': supports,
                        'selected_support': best, 'complete_shared_budget_upper': upper,
                        'actual_defect126_upper': prior_upper, 'budget_relaxation_excess': upper-prior_upper,
                        'chosen_actual_tail_gap': chosen_actual_tail-original_tail,
                        'all_omega_relaxation_lower': lower, 'support_optimality_gap': upper-lower['relaxation_lower'],
                        'maximizing_coordinate': affine.COORDINATES[coord], 'maximizing_witness': witness})
        print('Checked exhaustive shared budget at height '+str(case['height'])+': '+str(upper), flush=True)
    return encode({'schema': 'erdos7-exhaustive-shared-tail-cost-v1', 'source_sha256': {**PINS, **affine.PINS, **cost.PINS},
                   'cost_results': results,
                   'original_head_evaluations': sum(v['original_head_evaluations'] for r in results for v in r['exhaustive_vertices']),
                   'coordinate_fraction_checks': sum(v['coordinate_fraction_checks'] for r in results for v in r['exhaustive_vertices']),
                   'scope': 'Exhaustive all-original-head and common seven-coordinate/q-polygon upper for one complete AP cost at three fixed actual source data. Every selected support retains all infinite tails. Independent all-omega complete-series values certify all-cut optimality at heights5/8 and the face infimum. These are relaxed-envelope extrema, not actual-cost lower bounds. No uniform all-source comparison, new global K or Lean claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('exhaustive_tail_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact exhaustive shared-budget certificate')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: exhaustive original heads, all shared coordinates and polygon vertices, complete tails and correctly ordered supports.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
