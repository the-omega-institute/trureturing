#!/usr/bin/env python3
"""Complete geometric supports restore one shared convex defect optimization."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/shared_budget_affine_tail.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/comparison-bounds/complete_off_face_cost.py': 'ddc54ac54d21c00a885bfd0ab83adcaa31d4a9b4302844b2e432d069bac70ac7',
}
FAMILIES = ('pure3', 'pure5', 'root5', 'cell5')
DEFECTS = ('E5', 'E15', 'E3', 'E5d', 'E15d', 'omega')
COORDINATES = ('x5-g5*q5', 'x15-g15*q15', 'E27', 'Ege4', 'E5d', 'E15d', 'omega')


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


def rational(value):
    require(isinstance(value, (int, F)) and not isinstance(value, bool), 'Exact rational input')
    return F(value)


def punctured_support(prime, start, omitted, cut):
    """sum(n>=start,n not in omitted)min(e,H*p^-n) <= A*e+B*H."""
    require(isinstance(prime, int) and prime > 1 and isinstance(start, int) and start >= 0
            and isinstance(cut, int) and cut >= start, 'Integer complete-family cut')
    omitted = frozenset(omitted)
    require(all(isinstance(n, int) and n >= start for n in omitted), 'Removed original depths')
    A = cut-start-sum(n < cut for n in omitted)
    B = F(1, prime**cut)/(1-F(1, prime))-sum((F(1, prime**n) for n in omitted if n >= cut), F(0))
    L = F(1, prime**start)/(1-F(1, prime))-sum((F(1, prime**n) for n in omitted), F(0))
    require(A >= 0 and B >= 0 and L >= 0, 'Nonnegative complete support coefficients')
    return {'slope': F(A), 'intercept_coefficient': B, 'remaining_geometric': L}


def omissions(name, prefix):
    require(name in FAMILIES and isinstance(prefix, int) and 0 <= prefix <= 4, 'Original prefix')
    if name == 'pure3':
        return ({3} if prefix >= 2 else set()) | ({4} if prefix >= 4 else set())
    if name == 'pure5':
        return {2} if prefix >= 1 else set()
    if name == 'root5':
        return {2} if prefix >= 3 else set()
    return set()


def tail_affine(tail, record, cuts):
    """Fixed-source affine upper for every complete tail in one hinge cost.

    tail is125.complete_tails(...); record is116.prepare(...).
    cuts has four integer values, one per FAMILIES entry.
    """
    require(set(cuts) == set(FAMILIES) and tail['root0_raw_dominated'],
            'Four fixed cuts and the concentrated root1 dominance domain')
    coefficients = record['coefficients']
    require(coefficients and all(1 <= t <= 8 and a > 0 for t, a in coefficients.items()),
            'Nonzero nonnegative original hinge combination')
    parameters = {}
    for name in FAMILIES:
        row = tail['family_parameters'][name]
        if name == 'cell5':
            c = max(branch[0] for branch in row['branches'])
            H = row['raw']-c
        else:
            require(len(row['branches']) == 1, 'One dominated-family branch')
            c, _, H = row['branches'][0]
        parameters[name] = {'prime': row['prime'], 'start': row['start'], 'c': c, 'H': H}
    slopes, constant, detail = dict.fromkeys(FAMILIES, F(0)), F(0), {}
    for t, a in coefficients.items():
        k = record['prefix'][t]
        require(k == min(t-1, 4), 'Original selected-label prefix remains unchanged')
        rows = {}
        for name, row in parameters.items():
            support = punctured_support(row['prime'], row['start'], omissions(name, k), cuts[name])
            slopes[name] += a*support['slope']
            constant += a*(row['c']*support['remaining_geometric']+row['H']*support['intercept_coefficient'])
            rows[name] = support
        constant += a*(tail['raw_deep_mixed']+tail['positive7'])
        detail[t] = rows
    P3, P5, P1, Pc = (slopes[name] for name in FAMILIES)
    kappa = tail['root_wrong_price']
    source_offset = P5*(tail['z']-tail['family_parameters']['pure3']['raw'])/90
    constant += source_offset
    prices = dict(zip(DEFECTS, (P3, kappa*P3, P5, P3, kappa*P3, P3+P5+P1+Pc)))
    return {'constant': constant, 'defect_prices': prices, 'slopes': slopes,
            'kappa': kappa, 'cuts': dict(cuts), 'family_parameters': parameters,
            'source_offset': source_offset, 'punctured_supports': detail}


def evaluate_tail(envelope, defects):
    return envelope['constant']+sum(envelope['defect_prices'][k]*rational(defects[k]) for k in DEFECTS)


def branch_affine(envelope, record, mean, r, r1, g5, g15, rho, a0, survivor_mass):
    """Complete same-head support before the finite C_b is supplied.

    The seven residual coordinates are COORDINATES. No clipped mean credit
    is used, and Ma is the bounded transfer price, not a head supremum.
    """
    r, r1, g5, g15, rho, a0, survivor_mass = map(rational, (r, r1, g5, g15, rho, a0, survivor_mass))
    require(0 <= r1 <= r and g5 > 0 and g15 > 0 and survivor_mass >= 0, 'Actual positive packing domain')
    e0 = rho-(r+r1)/5
    require(e0 >= 0, 'One residual after the unavoidable shallow source losses')
    p = envelope['defect_prices']
    a1, Ma = record['coefficients'].get(1, F(0)), record['M']
    prices = (p['E5'], p['E15'], p['E3']+a1*mean['E27_price'],
              p['E3']+a1*mean['Ege4_price'], p['E5d']+a1*mean['E5deep_price'],
              p['E15d']+a1*mean['E15deep_price'], p['omega']+Ma)
    require(min(prices) >= 0, 'A nonnegative price allows unused residual to be assigned to a simplex vertex')
    constant = (a0*survivor_mass+envelope['constant']+(p['E5']*r+p['E15']*r1)/5
                -a1*(mean['reference']-mean['source_error']))
    return {'constant': constant, 'slot_prices': (p['E5']*g5, p['E15']*g15),
            'prices': prices, 'coordinates': COORDINATES, 'e0': e0, 'g5': g5, 'g15': g15,
            'constant_mass_term': a0*survivor_mass, 'bounded_transfer_price': Ma}


def residual(branch, q):
    q = tuple(map(rational, q))
    require(len(q) == 2 and min(q) >= 0 and max(q) <= F(1, 5), 'One actual pair of wrong-slot weights')
    e = branch['e0']-branch['g5']*q[0]-branch['g15']*q[1]
    require(e >= 0, 'One feasible common packing polygon')
    return e


def evaluate_branch(branch, finite_upper, q):
    e = residual(branch, q)
    return branch['constant']+rational(finite_upper)+sum(a*b for a, b in zip(branch['slot_prices'], q))+e*max(branch['prices'])


def shared_coordinate_upper(cost_branches, weights, q):
    """Each candidate is(branch_affine_data, its finite C_b at the same q).

    The result retains one common residual coordinate and one q, while
    each cost retains its own maximizing original head.
    """
    weights = tuple(map(rational, weights))
    require(len(cost_branches) == len(weights) and weights and min(weights) >= 0
            and all(cost_branches), 'Nonnegative cost weights and nonempty original heads')
    first = cost_branches[0][0][0]
    e = residual(first, q)
    require(all((b['e0'], b['g5'], b['g15'], b['coordinates']) ==
                (first['e0'], first['g5'], first['g15'], COORDINATES)
                for branches in cost_branches for b, _ in branches), 'One shared packing simplex for every cost')
    values = []
    for j in range(len(COORDINATES)):
        values.append(sum(beta*max(b['constant']+C+sum(a*x for a, x in zip(b['slot_prices'], q))+e*b['prices'][j]
                                  for b, C in branches)
                          for beta, branches in zip(weights, cost_branches)))
    return {'upper': max(values), 'coordinate_values': tuple(values), 'residual': e,
            'maximizing_coordinates': tuple(COORDINATES[j] for j, value in enumerate(values) if value == max(values))}


def support_checks(tails):
    checks, equalities, digest = 0, 0, sha256()
    for prime, start, omitted in ((3, 3, ()), (3, 3, (3,)), (3, 3, (3, 4)),
                                  (5, 2, ()), (5, 2, (2,)), (5, 2, (2, 5))):
        for e, H in product((F(0), F(1, 3125), F(1, 125), F(1, 20)), (F(0), F(1, 20), F(1, 10), F(2, 3))):
            exact = tails.complete_series(((F(0), e, H),), H, prime, start, omitted)
            if e > 0:
                support = punctured_support(prime, start, omitted, exact['crossing'])
                require(support['slope']*e+support['intercept_coefficient']*H == exact['upper'],
                        'A complete geometric crossing attains the infimum, including removed labels')
                equalities += 1
            for cut in range(start, start+9):
                support = punctured_support(prime, start, omitted, cut)
                upper = support['slope']*e+support['intercept_coefficient']*H
                require(upper >= exact['upper'], 'Every fixed cut majorizes the complete punctured family')
                if e == 0:
                    require(upper == H*support['intercept_coefficient'], 'Exact finite-cut zero-defect intercept')
                checks += 1
                digest.update(str((prime, start, omitted, e, H, cut, exact['upper'], upper)).encode())
    endpoint = F(1, 100)
    def wrong_order(e):
        return min(F(3, 2)*(endpoint-e)+punctured_support(5, 2, (), N)['slope']*e
                   +punctured_support(5, 2, (), N)['intercept_coefficient'] for N in (3, 4))
    interior = wrong_order(F(1, 125))
    vertices = max(wrong_order(F(0)), wrong_order(endpoint))
    safe = min(max(F(3, 2)*(endpoint-e)+punctured_support(5, 2, (), N)['slope']*e
                   +punctured_support(5, 2, (), N)['intercept_coefficient'] for e in (F(0), endpoint)) for N in (3, 4))
    require(interior == F(21, 1000) and vertices == F(1, 50) and safe == F(11, 500) and interior > vertices,
            'Taking the pointwise minimum of supports invalidates vertex-only maximization')
    return {'support_checks': checks, 'exact_crossing_equalities': equalities, 'digest': digest.hexdigest(),
            'support_order_refutation': {'interval': (F(0), endpoint), 'interior': F(1, 125),
                 'interior_value': interior, 'incorrect_vertex_upper': vertices, 'valid_fixed_support_upper': safe}}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('affine_tail_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    cost = module('affine_tail_cost', base/'frontier/comparison-bounds/complete_off_face_cost.py')
    for path, pin in cost.PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned cost input '+path)
    finite = module('affine_tail_finite', base/'frontier/retained-transport/finite_source_face_transport.py')
    mean = module('affine_tail_mean', base/'frontier/retained-transport/joint_deep_mean_transport.py')
    tails = module('affine_tail_complete', base/'frontier/cover-geometry/complete_off_face_omitted_tails.py')
    source = module('affine_tail_source', base/'verify_joint_frontier.py')
    old = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/whole_cost_mean_stop_loss.json'))
    rows = old['cost_results'][1:3]
    records = [finite.prepare({int(t): F(a) for t, a in row['objective']['coefficients'].items()}) for row in rows]
    weights = (F(2, 3), F(3, 5))
    layouts = ((0, 1, 2, 0, 2, 1, 2), (1, 0, 0, 0, 0, 1, 1),
               (1, 3, 4, 1, 2, 0, 3), (0, 2, 1, 1, 4, 4, 1))
    cases = [cost.face_case(finite, source)]+[cost.actual_398_case(finite, source, h) for h in (5, 8)]
    outputs, tail_checks, branch_checks, sharing_checks, convex_checks = [], 0, 0, 0, 0
    for case in cases:
        tail = tails.complete_tails(case['dat'], case['pi'], case['defects'], case['parameter'][4])
        cuts = {name: max(10 if case['height'] is None else 2, tail['complete_series'][0][name]['crossing']) for name in FAMILIES}
        envelopes = [tail_affine(tail, record, cuts) for record in records]
        tail_results = []
        for envelope, record in zip(envelopes, records):
            original = sum(a*(tail['old_remainders'][record['prefix'][t]]+tail['positive7']) for t, a in record['coefficients'].items())
            upper = evaluate_tail(envelope, case['defects'])
            require(upper >= original, 'Complete weighted tail majorization at one actual source')
            tail_results.append({'original': original, 'affine_upper': upper, 'difference': upper-original,
                                 'envelope': envelope})
            tail_checks += 1
        d, n, eta, s, _ = case['dat']
        caps = case['point']['caps']
        h, h1 = sum(eta), sum(eta[2:])
        g5 = h/5-max(sum(caps[5*l+j] for l in range(5)) for j in range(4))
        g15 = h1/5-max(max(sum(caps[5*l+j] for l in range(2, 5)) for j in range(4)),
                         max(sum(caps[5*l+j] for l in range(2)) for j in range(5)))
        require(g5 > 0 and g15 > 0, 'Actual source cap table certifies positive wrong-slot gaps')
        defects, q_actual = case['defects'], case['q']
        require(defects['E5'] >= g5*q_actual[0] and defects['E15'] >= g15*q_actual[1],
                'Actual full shallow defects pay the certified wrong-slot prices')
        head_data = [mean.mean_data(case['sigma'], max(d), max(d[2:]), case['parameter'][4], eta, case['qslots'], layout) for layout in layouts]
        supports = [[branch_affine(envelope, record, data, F(0), F(0), g5, g15,
                                   defects['rho'], F(row['constant_mass_term']), case['survivor_mass'])
                     for data in head_data] for envelope, record, row in zip(envelopes, records, rows)]
        cache = {}
        def at(q):
            nonlocal sharing_checks
            if q in cache:
                return cache[q]
            candidates = []
            for record, heads in zip(records, supports):
                compiler = cost.IntegerHead(finite, record, case['point'], q)
                candidates.append(tuple((support, F(compiler.branch(compiler.load(layout), extra), compiler.scale))
                                        for support, layout in zip(heads, layouts)
                                        for r, j, extra in compiler.positive7 if (r, j) in ((0, 2), (1, 4))))
            result = shared_coordinate_upper(candidates, weights, q)
            e = result['residual']
            brute = max(sum(beta*(b['constant']+C+sum(a*x for a, x in zip(b['slot_prices'], q)))
                            for beta, (b, C) in zip(weights, choice))
                        +e*max(sum(beta*b['prices'][j] for beta, (b, C) in zip(weights, choice)) for j in range(7))
                        for choice in product(*candidates))
            require(result['upper'] == brute, 'One shared coordinate equals the full independent-head tuple optimization')
            separate = sum(beta*max(evaluate_branch(b, C, q) for b, C in branches)
                           for beta, branches in zip(weights, candidates))
            require(result['upper'] <= separate, 'Separate cost residual allowances cannot improve the shared bound')
            sharing_checks += 1
            cache[q] = (result, candidates, separate)
            return cache[q]
        observed = at(q_actual)
        for envelope, record, row, candidates in zip(envelopes, records, rows, observed[1]):
            for i, (branch, C) in enumerate(candidates):
                mean_data = head_data[i//2]
                credit = mean.mean_credit(mean_data, case['E27'], defects['E3']-case['E27'], defects['E5d'], defects['E15d'])['nonnegative_credit']
                original = (F(row['constant_mass_term'])*case['survivor_mass']+C-record['coefficients'].get(1, F(0))*credit
                            +sum(a*(tail['old_remainders'][record['prefix'][t]]+tail['positive7']) for t, a in record['coefficients'].items())
                            +record['M']*defects['omega'])
                require(original <= evaluate_branch(branch, C, q_actual), 'Complete same-original-head cost is bounded after one shared budget elimination')
                branch_checks += 1
        vertices = finite.defect_vertices(g5, g15, defects['rho'])
        vertex_values = [(q, at(q)[0]['upper']) for q in vertices]
        for q0, q1 in combinations(vertices, 2):
            qm = tuple((a+b)/2 for a, b in zip(q0, q1))
            require(at(qm)[0]['upper'] <= (at(q0)[0]['upper']+at(q1)[0]['upper'])/2,
                    'Fixed-source fixed-support weighted objective obeys Jensen across polygon vertices')
            convex_checks += 1
        vertex_upper = max(value for q, value in vertex_values)
        require(observed[0]['upper'] <= vertex_upper, 'Actual common slot weights fit the complete fixed-support polygon bound')
        outputs.append({'height': case['height'], 'cuts': cuts, 'tail_results': tail_results,
                        'g5': g5, 'g15': g15, 'actual_slots': q_actual, 'actual_shared_upper': observed[0],
                        'actual_separate_budget_upper': observed[2], 'vertex_values': vertex_values,
                        'restricted_head_vertex_upper': vertex_upper, 'heads_per_cost': len(observed[1][0]),
                        'scope': 'Exact restricted-head regression; not an exhaustive original-head or all-source numerical bound.'})
    return encode({'schema': 'erdos7-shared-budget-affine-tail-v1', 'source_sha256': {**PINS, **cost.PINS},
                   'support_algebra': support_checks(tails), 'actual_cases': outputs,
                   'complete_tail_checks': tail_checks, 'same_head_cost_checks': branch_checks,
                   'shared_coordinate_equalities': sharing_checks, 'jensen_checks': convex_checks,
                   'scope': 'Ordinary complete-tail affine support theorem and common-coordinate cost reduction. Infinite tails retained. Exact finite arithmetic supplements the general proof; no new global K or Lean claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('affine_tail_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact semantic shared affine-tail certificate')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: complete punctured geometric supports, shared seven-coordinate cost reduction, actual-source and support-order checks.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
