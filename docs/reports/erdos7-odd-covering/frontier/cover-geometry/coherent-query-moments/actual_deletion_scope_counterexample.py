"""Exact sparse controls for the actual-deletion prime-scope construction.

The ordinary proof handles arbitrary k and tau. This consumer checks the
fixed k=2 realization at tau=0 and 1/29^4 and declared failure controls.
It never scans the CRT carrier or the query phase-product space.
"""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import argparse
import json
import signal

CHECKS = Counter()
PRIMES = (3, 5)
R_PRIME, Q_PRIME = 7, 11
H, NONUNIT_QUERIES, HIGH_LOAD = 16, 28, 29
TAUS = (F(0), F(1, 29**4))


def need(ok, label):
    CHECKS[label] += 1
    if not ok:
        raise ValueError(label)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON key: ' + key)
        result[key] = value
    return result


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def crt(components):
    value, modulus = 0, 1
    for residue, next_modulus in components:
        need(next_modulus > 1 and 0 <= residue < next_modulus, 'CRT component range')
        need(gcd(modulus, next_modulus) == 1, 'coprime CRT coordinates')
        value += modulus * (((residue-value) * pow(modulus, -1, next_modulus)) % next_modulus)
        modulus *= next_modulus
    need(0 <= value < modulus, 'normalized CRT residue')
    for residue, component_modulus in components:
        need(value % component_modulus == residue, 'literal CRT component')
    return value, modulus


def validate_points(points):
    need(len({p['residue'] for p in points}) == len(points), 'distinct source positions')


def validate_labels(originals):
    labels = [row['modulus'] for row in originals]
    need(len(set(labels)) == len(labels), 'distinct numerical original labels')
    need(all(d > 1 and d % 2 == 1 for d in labels), 'odd nonunit original labels')


def validate_phase_claim(modulus, phase, residues):
    need(0 <= phase < modulus, 'normalized globally fixed query phase')
    need(all(x % modulus == phase for x in residues), 'one phase realizes the whole claimed incidence')


def geometry():
    all_primes = (*PRIMES, R_PRIME, Q_PRIME)
    need(len(set(all_primes)) == len(all_primes) and all(prime(p) and p % 2 for p in all_primes), 'exact distinct odd control primes')
    k, n = len(PRIMES), 2**(len(PRIMES)-1)
    M = prod(PRIMES)
    period = M * R_PRIME**n * Q_PRIME**NONUNIT_QUERIES
    vectors = tuple(product((0, 1), repeat=k))
    points = []
    for v in vectors:
        residue, modulus = crt([*zip(v, PRIMES), (0, R_PRIME**n), (0, Q_PRIME**NONUNIT_QUERIES)])
        need(modulus == period, 'one common source carrier')
        points.append({'name': ''.join(map(str, v)), 'vector': v, 'r': 0, 'q': 0, 'residue': residue})
    zero = (0,) * k
    residue, modulus = crt([*zip(zero, PRIMES), (1, R_PRIME**n), (0, Q_PRIME**NONUNIT_QUERIES)])
    need(modulus == period, 'background on same source carrier')
    points.append({'name': 'background', 'vector': zero, 'r': 1, 'q': 0, 'residue': residue})
    validate_points(points)
    originals, masks = {}, {}
    for parity, name in ((0, 'D_even'), (1, 'D_odd')):
        chosen = [v for v in vectors if sum(v) % 2 == parity]
        need(len(chosen) == n, 'equal parity cardinalities')
        rows = []
        for j, v in enumerate(chosen, 1):
            phase, modulus = crt([*zip(v, PRIMES), (0, R_PRIME**j)])
            need(modulus == M*R_PRIME**j and period % modulus == 0, 'same indexed original inventory')
            hits = [i for i, point in enumerate(points) if point['residue'] % modulus == phase]
            need(hits == [vectors.index(v)], 'one cube private point and no background hit')
            rows.append({'modulus': modulus, 'phase': phase, 'vector': v, 'source_hits': hits})
        validate_labels(rows)
        for i, row in enumerate(rows):
            for other in rows[i+1:]:
                need((row['phase']-other['phase']) % gcd(row['modulus'], other['modulus']) != 0,
                     'actual whole original classes CRT-disjoint')
        originals[name] = rows
        masks[name] = [any(point['residue'] % row['modulus'] == row['phase'] for row in rows) for point in points]
        need(not masks[name][-1] and sum(masks[name]) == n, 'actual parity deletion and background survival')
    need([r['modulus'] for r in originals['D_even']] == [r['modulus'] for r in originals['D_odd']], 'literal equal original numerical inventories')
    query_labels = [M * Q_PRIME**j for j in range(1, NONUNIT_QUERIES+1)]
    need(len(set(query_labels)) == 28 and all(d > 1 and d % 2 and period % d == 0 for d in query_labels), 'distinct actual query labels in carrier')
    need(not set(query_labels).intersection(row['modulus'] for row in originals['D_even']), 'query and original tag axes distinct')
    # Every possible query phase is classified by its M residue and q residue.
    # Only the four binary M residues and zero q residue can meet this source.
    cube_phase = {v: crt(list(zip(v, PRIMES)))[0] for v in vectors}
    query_incidence = []
    for j, d in enumerate(query_labels, 1):
        classes = {}
        for i, point in enumerate(points):
            classes.setdefault(point['residue'] % d, []).append(i)
        need(len(classes) == len(vectors), 'all nonempty query incidence classes')
        phase_rows = []
        for v in vectors:
            phase, modulus = crt([(cube_phase[v], M), (0, Q_PRIME**j)])
            need(modulus == d, 'query literal numerical modulus')
            expected = [i for i, point in enumerate(points) if point['vector'] == v]
            need(classes.get(phase) == expected, 'query phase hits exactly one cube cluster')
            validate_phase_claim(d, phase, [points[i]['residue'] for i in expected])
            phase_rows.append({'vector': v, 'phase': phase, 'source_hits': expected})
        miss_phase, _ = crt([(cube_phase[zero], M), (1, Q_PRIME**j)])
        need(miss_phase not in classes, 'nonzero q-phase misses source')
        query_incidence.append({'modulus': d, 'cluster_phases': phase_rows, 'miss_phase': miss_phase})
    return {'k': k, 'n': n, 'M': M, 'period': period, 'points': points, 'vectors': vectors,
            'originals': originals, 'masks': masks, 'queries': query_incidence}


def histogram(points, weights, cube_axes):
    table = {}
    for point, weight in zip(points, weights):
        if weight:
            key = tuple(point['vector'][j] for j in cube_axes) + (point['r'], point['q'])
            table[key] = table.get(key, F(0)) + weight
    return table


def clusters(points, weights):
    out = {}
    for point, weight in zip(points, weights):
        out[point['vector']] = out.get(point['vector'], F(0)) + weight
    return out


def hinge(load):
    return max(F(0), F(load-H))


def verify_chords():
    for t in range(29):
        for name, value, low, high in (
                ('hinge', hinge(1+t), hinge(1), hinge(29)),
                ('fourth', F((1+t)**4), F(1), F(29**4))):
            need(value <= low + F(t, 28)*(high-low), name+' convex chord for every possible integer hit count')
    need(hinge(29) == 13 and hinge(1) == 0, 'unit-inclusive hinge endpoints')


def attaining(g, weights, chosen=None):
    c = clusters(g['points'], weights)
    chosen = max(c, key=lambda v: (c[v], tuple(-x for x in v))) if chosen is None else chosen
    layout = []
    for query in g['queries']:
        row = next(row for row in query['cluster_phases'] if row['vector'] == chosen)
        layout.append((query['modulus'], row['phase']))
    loads = [1 + sum(point['residue'] % d == phase for d, phase in layout) for point in g['points']]
    need(all(load == (29 if point['vector'] == chosen else 1) for point, load in zip(g['points'], loads)), 'actual globally phased attaining loads')
    H_value = sum((weight*hinge(load) for weight, load in zip(weights, loads)), F(0))
    K_value = sum((weight*load**4 for weight, load in zip(weights, loads)), F(0))
    return c, chosen, loads, layout, H_value, K_value


def main_examples(g):
    records = []
    for tau in TAUS:
        A, B, C = 12-tau, 13+(29**4-1)*tau, 1+29**4*tau
        need(F(0) <= tau < 12 and A*g['n'] > B/2+C, 'declared parameter domain')
        b = (A*g['n']-B/2)/C
        need(b > 1 and C == B-A, 'background choice and exact coefficient identity')
        prior = [F(1)]*len(g['vectors']) + [b]
        prior_mass = sum(prior)
        survivors = {name: [F(0) if hit else weight for weight, hit in zip(prior, mask)] for name, mask in g['masks'].items()}
        alpha = g['n']+b
        for name, weights in survivors.items():
            need(sum(weights) == alpha and prior_mass-alpha == g['n'], 'same exact survivor and deletion masses')
            for row in g['originals'][name]:
                need(sum(prior[i] for i in row['source_hits']) == 1, 'each labelled original has mass one')
        marginal_rows = []
        for flags in product((False, True), repeat=g['k']):
            axes = [j for j, flag in enumerate(flags) if flag]
            if len(axes) == g['k']:
                continue
            left = histogram(g['points'], survivors['D_even'], axes)
            right = histogram(g['points'], survivors['D_odd'], axes)
            need(left == right, 'all proper cube scopes with full auxiliary coordinates agree')
            marginal_rows.append({'cube_axes': axes, 'auxiliary_axes': ['r^n','q^28'],
                                  'histogram': [[key, value] for key, value in sorted(left.items())]})
        cases = {}
        for name, weights in survivors.items():
            c, chosen, loads, layout, hv, kv = attaining(g, weights)
            wmax = max(c.values())
            expected_max = b if name == 'D_even' else b+1
            need(wmax == expected_max and chosen == (0,)*g['k'], 'correct surviving maximum cluster')
            need(hv == 13*wmax and kv == alpha+(29**4-1)*wmax, 'both independently attained global-max formulas')
            gate = 12*alpha-hv-tau*kv
            expected = B/2 if name == 'D_even' else -B/2
            need(gate == expected, 'opposite exact joint numerator')
            need((gate > 0) == (name == 'D_even') and gate/prior_mass == expected/prior_mass, 'common probability normalization preserves sign')
            cases[name] = {'survivor_weights': weights, 'cluster_masses': [[v, value] for v, value in sorted(c.items())],
                           'attaining_cube_vector': chosen, 'attaining_layout': layout, 'source_loads': loads,
                           'maximum_hinge16': hv, 'maximum_fourth': kv, 'joint_gate': gate,
                           'normalized_joint_gate': gate/prior_mass}
        need(dict((tuple(v), w) for v,w in cases['D_odd']['cluster_masses'])[(0,)*g['k']] -
             dict((tuple(v), w) for v,w in cases['D_even']['cluster_masses'])[(0,)*g['k']] == 1, 'full cube scope separates survivors')
        records.append({'tau': tau, 'A': A, 'B': B, 'C': C, 'background_weight': b,
                        'prior_weights': prior, 'prior_mass': prior_mass, 'survivor_mass': alpha,
                        'proper_scope_marginals': marginal_rows, 'scenarios': cases})
    return records


def expected_failure(name, action):
    try:
        action()
    except ValueError as error:
        return {'control': name, 'rejected_by': str(error)}
    raise ValueError('mutation not rejected: ' + name)


def controls(g, records):
    out = []
    bad_points = [dict(point) for point in g['points']]
    bad_points[-1]['residue'] = bad_points[0]['residue']
    out.append(expected_failure('background_original_tag_lost', lambda: validate_points(bad_points)))
    bad_originals = [dict(row) for row in g['originals']['D_even']]
    bad_originals[1]['modulus'] = bad_originals[0]['modulus']
    out.append(expected_failure('duplicate_numerical_original', lambda: validate_labels(bad_originals)))
    d = g['queries'][0]['modulus']
    out.append(expected_failure('cellwise_query_phase', lambda: validate_phase_claim(d, g['points'][0]['residue'] % d,
                                                                                   [g['points'][0]['residue'],g['points'][1]['residue']])))
    example = records[0]['scenarios']['D_even']
    without_unit = sum((w*hinge(load-1) for w,load in zip(example['survivor_weights'],example['source_loads'])),F(0))
    out.append(expected_failure('unit_omitted', lambda: need(without_unit == example['maximum_hinge16'], 'unit omission changes attaining hinge')))
    small_prior = [F(1)]*len(g['vectors']) + [F(1,2)]
    raw_clusters = clusters(g['points'],small_prior)
    need(max(raw_clusters,key=raw_clusters.get) == (0,)*g['k'], 'switch control old maximizer is zero')
    switched = [F(0) if hit else w for w,hit in zip(small_prior,g['masks']['D_even'])]
    c, chosen, _, _, new_h, new_k = attaining(g,switched)
    _, _, _, _, old_h, old_k = attaining(g,switched,(0,)*g['k'])
    need(chosen != (0,)*g['k'] and max(c.values()) == 1 and c[(0,)*g['k']] == F(1,2), 'maximizer changes under actual deletion')
    need(old_h < new_h and old_k < new_k, 'old maximizing phase underestimates both survivor maxima')
    out.append(expected_failure('frozen_old_maximizer', lambda: need(c[(0,)*g['k']] == max(c.values()), 'old cluster is not a final-law maximizer')))
    full_left = histogram(g['points'],records[0]['scenarios']['D_even']['survivor_weights'],list(range(g['k'])))
    full_right = histogram(g['points'],records[0]['scenarios']['D_odd']['survivor_weights'],list(range(g['k'])))
    out.append(expected_failure('proper_scope_promoted_to_full', lambda: need(full_left == full_right, 'full cube marginals differ')))
    symbolic_primes = (3,5,7,11,17)
    need(len(set(symbolic_primes)) == 5 and all(prime(p) for p in symbolic_primes), 'exact primes for algebraic support control')
    label = prod(symbolic_primes)
    need(lcm(label,label,label,label) == label and all(label % p == 0 for p in symbolic_primes), 'four equal query labels retain entire numerical prime support')
    out.append(expected_failure('tuple_order_promoted_to_prime_scope', lambda: need(len(symbolic_primes) <= 4, 'fourth order does not bound prime-coordinate scope')))
    need(len(out) == 7, 'all declared material failure controls rejected')
    return {'rejections': out, 'optimizer_switch': {'background_weight': F(1,2), 'surviving_zero_mass': F(1,2),
              'surviving_maximum_mass': F(1), 'old_phase_hinge': old_h, 'maximum_hinge': new_h,
              'old_phase_fourth': old_k, 'maximum_fourth': new_k},
            'algebraic_support': {'four_tuple': [label]*4,'lcm':label,'distinct_prime_axes':list(symbolic_primes)}}


def result():
    g = geometry()
    verify_chords()
    records = main_examples(g)
    mutation_controls = controls(g,records)
    need(sum(CHECKS.values()) <= 2000, 'bounded exact control count')
    return encode({'schema':'e7-actual-deletion-scope-counterexample-v1', 'status':'pass',
        'evidence':'ordinary proof plus exact sparse controls; no Lean claim',
        'consumer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'geometry':{'k':g['k'],'n':g['n'],'cube_primes':PRIMES,'original_tag_prime_r':R_PRIME,'query_tag_prime_q':Q_PRIME,
          'period':g['period'],'source_positions':g['points'],'actual_originals':g['originals'],
          'query_inventory':[1]+[row['modulus'] for row in g['queries']]},
        'main_examples':records,'failure_controls':mutation_controls,
        'global_maximum_proof_interface':'Convex chord on[1,29], sum of per-cluster hits<=28, and one actual globally fixed attaining layout; no phase-product enumeration.',
        'scope':'same prior per tau; actual original labels fixed, phases fixed within each scenario; equal marginals on scopes missing at least one cube prime, not every proper subset of all carrier axes',
        'boundaries':['finite declared29-label query family only; not its full-divisor or all-height completion',
                      'not fixedC/phase31 and not an Erdos7 result',
                      'fourth moment tuple order is not the number of prime coordinates in one numerical label'],
        'searches':{'optimizers':0,'phase_layout_scans':0,'carrier_scans':0,'source_points':5,'main_tau_values':2},
        'checks':dict(CHECKS),'checks_total':sum(CHECKS.values())})


def timeout(signum, frame):
    raise TimeoutError('fixed 30-second sparse-control bound exceeded')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--result',type=Path,default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--write-result',action='store_true')
    args = parser.parse_args()
    signal.signal(signal.SIGALRM,timeout)
    signal.alarm(30)
    actual = result()
    if args.write_result:
        with args.result.open('x') as stream:
            json.dump(actual,stream,indent=2,sort_keys=True)
            stream.write('\n')
    else:
        expected = json.loads(args.result.read_text(),object_pairs_hook=unique)
        need(expected == actual,'complete deterministic saved-result comparison')
    signal.alarm(0)
    print(json.dumps({'status':'pass','checks_total':actual['checks_total'],
          'main_tau_values':actual['searches']['main_tau_values'],
          'failure_controls_rejected':len(actual['failure_controls']['rejections']),
          'result_sha256':sha256(args.result.read_bytes()).hexdigest(),
          'action':'written' if args.write_result else 'compared'},indent=2))


if __name__ == '__main__':
    main()
