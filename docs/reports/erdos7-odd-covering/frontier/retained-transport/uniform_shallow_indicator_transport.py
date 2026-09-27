#!/usr/bin/env python3
"""Independent shallow indicators with actual H-column identities and one residual."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
from types import SimpleNamespace
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/uniform_shallow_indicator_transport.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/comparison-bounds/uniform_k_neighborhood_cost.py': '365265347aca1ee5a179df991be2316219f0cb4dbe7a5606a020664c3a56723b',
    'frontier/moments-survival/uniform_ap_survival_denominator.py': '181a1793bd15059074d2998eb820322a3b9c2158bac5edfcb3bc057b7e78f180',
    'frontier/cover-geometry/uniform_square_and_raw81_neighborhood.py': '3d47bd0d7ff5f5c4f8114d02538073de8bc87e455265817e9e9d80ca4bc5a62c',
    'frontier/retained-transport/finite_source_face_transport.py': '04c99f1a0c6e1781734531923705863fbc9843c610f6d4933a81c89429aa5291',
    'frontier/endpoint-bounds/broad_weighted_identity_source.py': 'bfc5f98109c02b318ee3e92c0951d1d33ded45971d6718623d4c60629dc2e6e6',
    'frontier/comparison-bounds/complete_off_face_cost.py': '0d53ac6dc99eac6db322525d94375c498e61cb1c5cacd8776327c70d311306c8',
    'frontier/moments-survival/complete_off_face_factorial_tail.py': '6f09199dd8379336bbc84e4245c3ea95a0499939cf72a2c41b9ef7b658049498',
    'frontier/cover-geometry/complete_off_face_omitted_tails.py': '33e8c164c64790483ba512c984e8090cf5c44b92bf6ca1cb08a17cb56a93201d',
    'frontier/cover-geometry/quantitative_forced27.py': '23551c4ae4b01624be33175524899b97f34464ea4b6383dda56ecc408128a947',
    'frontier/source-budgets/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645',
    'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765',
}
ROOT = (0, 0, 1, 1, 1)
ETA = (F(1, 18),)+(F(1, 9),)*4
QSLOTS = (F(0), F(1, 5), F(1, 5), F(3, 20), F(1, 5))
FACE = {3: F(7, 90), 9: F(1, 18), 5: F(14, 225), 15: F(8, 225), 45: F(4, 225)}
COORDINATES = ('E5-gq5', 'E15-gq15', 'E27', 'Ege4', 'E5deep', 'E15deep', 'omega')
_CACHE = {}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def get(name):
    if name not in _CACHE:
        base = Path(__file__).resolve().parents[2]
        _CACHE[name] = module('shallow_'+name, module('named_artifact_io', base/'certificate_io.py').named_artifact(base/'frontier', name+'.py'))
    return _CACHE[name]


def labels():
    return ([(3, r, None) for r in range(2)]+[(9, c, None) for c in range(5)]
            +[(5, None, j) for j in range(5)]
            +[(15, r, j) for r, j in product(range(2), range(5))]
            +[(45, c, j) for c, j in product(range(5), repeat=2)])


def indicator(label):
    m, a, j = label
    return tuple(F(int(ROOT[c] == a if m == 3 else c == a if m == 9 else s == j if m == 5
                       else ROOT[c] == a and s == j if m == 15 else c == a and s == j))
                 for c, s in product(range(5), repeat=2))


def reference(label, eta=ETA, qslots=QSLOTS):
    m, a, _ = label
    phi = indicator(label)
    g = tuple(min(phi[5*c+j] for c in (0, 1)) for j in range(5))
    f = tuple(phi[5+j] for j in range(5))
    require(all(y >= x for x, y in zip(g, f)), 'The ideal cell1 contains the retained root0 head')
    A3 = sum(q*x for q, x in zip(qslots, g))/90
    A27 = sum(q*(y-x) for q, x, y in zip(qslots, g, f))/135
    A5 = ((1+a)*sum(eta[c] for c in range(5) if ROOT[c] == a)/100 if m == 3 else
          (1+ROOT[a])*eta[a]/100 if m == 9 else F(0))
    return {'g': g, 'f': f, 'pure3': A3+A27, 'deep5': A5, 'total': A3+A27+A5}


def indicator_prices(label, par):
    """Project each actual original27 carrier; never import a five-indicator supremum."""
    m, a, j = label
    phi, ref = indicator(label), reference(label)
    g, f = ref['g'], ref['f']
    low1 = tuple(min(phi[5*c+s] for c in (2, 3, 4)) for s in range(5))
    N0 = max(F(0), *(f[s]-phi[s] for s in range(5)))
    N1 = max(F(0), *(f[s]-low1[s] for s in range(5)))
    Ng = max(F(0), *(g[s]-low1[s] for s in range(5)))
    L27 = max(f)+max(N0*(par['Cbar']-1), N1*par['tbar'])
    Lge4 = max(g)+Ng*par['tbar']
    deep5 = F(int(m in (3, 9)))
    deep15 = par['kbar']*int((m == 3 and a == 1) or (m == 9 and ROOT[a] == 1))
    # Signed slot identity133: constants in j belong to z, not to the slot weights.
    slot_weight = F(1, 90) if m == 5 or (m == 15 and a == 0) else F(1, 135) if m == 45 and a == 1 else F(0)
    v = tuple(slot_weight*int(s == j) for s in range(5))
    dA, dB, dH = (max(v[s]-v[3], F(0)) for s in (1, 2, 4))
    a5_loss = (F(1, 900) if m == 3 and a == 1 else
               F(1, 1800) if m == 9 and a == 1 else
               F(1, 900) if m == 9 and a in (2, 3, 4) else F(0))
    X_price = (max(g)/270+max(f)/135)*F(3, 8)
    source_price = a5_loss+(dA+dB)/4+X_price
    prices = (10*dH, F(0), L27, Lge4, deep5, deep15, F(1))
    require(max(prices) <= par['Cbar'] and source_price <= F(1, 144),
            'Independent-indicator prices, including the retained H/Q loss')
    return {'label': label, 'reference': ref['total'], 'source_delta_price': source_price,
            'source_discrepancy_price': max(g)/270+max(f)/135,
            'slot_weights': v, 'slot_migration_price': 10*dH,
            'wrong_cell_supremum': N0, 'wrong_root_supremum': N1,
            'coordinate_prices_before_finite_transport': prices}


def face_point(first_beta):
    finite = get('finite_source_face_transport')
    parameter = ((F(1, 2), F(0), F(0), F(0), F(0)), (F(0), F(1, 4)),
                 tuple(F(1, 4) if c == first_beta else F(0) for c in range(5)),
                 (F(1, 72), F(0), F(0), F(0), F(0)), F(3, 4))
    pi = tuple(F(int(c == (1, 1))) for c in finite.CARRIERS)
    return finite.source_point(parameter, pi, F(0), first_beta, F(0))


def face_audit():
    finite, capacity = get('finite_source_face_transport'), get('broad_weighted_identity_source')
    rows, summaries = [], []
    for L in (2, 3, 4):
        point = face_point(L)
        w = finite.weights(point, (F(0), F(0)))
        maximum = {}
        for label in labels():
            phi, ref = indicator(label), reference(label)['total']
            z = tuple(x*y for x, y in zip(w, phi))
            primal_dual = [capacity.capacity_dual(z, point['caps'], N, group)
                           for N, group in zip(point['budgets'], finite.GROUPS)]
            lp = sum(row[0] for row in primal_dual)
            repaired = (F(79, 900) if label[1] == 0 else F(19, 225)) if label[0] == 3 else lp
            value = repaired-ref
            require(value <= FACE[label[0]], 'DP14 repairs the original cap for every independent residue')
            rows.append({'first_beta': L, 'label': label, 'generic_lp': lp, 'face_credit': ref,
                         'generic_upper': lp-ref, 'valid_finite_face': repaired, 'valid_upper': value,
                         'group_duals': tuple(row[1] for row in primal_dual)})
            maximum[label[0]] = max(maximum.get(label[0], F(0)), lp-ref)
        require(maximum == {**FACE, 3: F(2, 25)}, 'Only the root0 mod3 cap fails generic trimming')
        summaries.append({'first_beta': L, 'generic_maxima': maximum})
    require(len(rows) == 141 and F(2, 25)-FACE[3] == F(1, 450), 'Exactly47 independent residues times3 first-beta cells')
    witness = [F(0)]*25
    for c, j, v in ((0, 1, F(1, 90)), (0, 2, F(1, 90)), (0, 3, F(1, 180)),
                    (1, 1, F(1, 45)), (1, 2, F(1, 45)), (1, 3, F(1, 60)), (1, 4, F(1, 45)),
                    (2, 3, F(1, 90)), (2, 4, F(1, 45)), (3, 2, F(1, 45)), (3, 3, F(1, 90)),
                    (3, 4, F(1, 45)), (4, 2, F(1, 45)), (4, 3, F(1, 90)), (4, 4, F(1, 60))):
        witness[5*c+j] = v
    p = face_point(2)
    require(all(0 <= v <= u for v, u in zip(witness, p['caps']))
            and tuple(sum(witness[i] for i in group) for group in finite.GROUPS) == p['budgets'],
            'Literal rational three-group relaxation witness')
    require(sum(witness[5*c+4] for c in (0, 1)) == F(1, 45) != F(1, 30),
            'The failed relaxation discarded the actual root0 H identity')
    return {'layouts_per_first_beta': 47, 'total_layouts': len(rows), 'rows': rows,
            'generic_maxima': summaries, 'root0_obstruction': F(1, 450), 'relaxation_witness': witness}


def source_caps(point, delta, hmin):
    """Separate source increments from r; the latter will be charged inside y1."""
    caps, r_slopes = [], []
    for i, original in enumerate(point['caps']):
        c, j = divmod(i, 5)
        excluded = j == 0 or (c >= 2 and j == 1) or (c == point['first_beta'] and j == 2)
        inc = F(0) if excluded else delta/90 if c == 0 else F(0)
        rs = F(0)
        if j == 3:
            inc += delta/24 if c == 0 else delta/12
            rs = F(1, 9) if c == 0 else F(2, 9) if c == 1 else 1/(9*hmin)
        caps.append(original+inc)
        r_slopes.append(rs)
    budgets = tuple(a+b for a, b in zip(point['budgets'],
                    ((5*delta+delta**2)/72, delta/36, 5*delta/24-delta**2/72)))
    return tuple(caps), tuple(r_slopes), budgets


def one_label_bound(label, first_beta, par):
    d, rho, gap = par['delta'], par['rho'], par['gap']
    finite, capacity = get('finite_source_face_transport'), get('broad_weighted_identity_source')
    point, phi = face_point(first_beta), indicator(label)
    record = indicator_prices(label, par)
    prices = list(record['coordinate_prices_before_finite_transport'])
    if label[0] == 3:
        if label[1] == 0:
            finite_upper = F(79, 900)+(5*d+d*d)/72+(4+d)*d/180+d/60
            prices[0] += 1
            qprice = (F(1, 6)+d/18)/5
        else:
            finite_upper = F(19, 225)+(4+d)*(5*d/24-d*d/72)/5+d/36+d/225
            prices[1] += 2
            qprice = F(1, 15)
        finite_record = {'method': 'actual DP14 simultaneous H-column identities', 'finite_upper': finite_upper}
    else:
        caps, r_slopes, budgets = source_caps(point, d, par['h1min'])
        wstar = finite.weights(point, (F(0), F(0)))
        z = tuple((wstar[i]+d*F(int(i//5 != 0), 5))*phi[i] for i in range(25))
        duals = [capacity.capacity_dual(z, caps, N, group) for N, group in zip(budgets, finite.GROUPS)]
        finite_upper = sum(v for v, _ in duals)
        rprice = sum(r_slopes[i]*max(z[i]-gamma, F(0))
                     for (_, gamma), group in zip(duals, finite.GROUPS) for i in group)
        # A fixed dual remains feasible after adding the actual r cap increments.
        # r<=5*y1, so this price and the slot migration price ADD on that coordinate.
        prices[0] += 5*rprice
        qprice = max(sum((ETA[c]+(d/18 if c == 0 else 0))*phi[5*c+4]/5 for c in range(5)),
                     sum(ETA[c]*phi[5*c+4]/5 for c in (2, 3, 4)))
        finite_record = {'method': 'fixed source-only capacity dual, residual cap change on y1',
                         'finite_upper': finite_upper, 'group_duals': tuple(v[1] for v in duals),
                         'source_only_caps': caps, 'source_only_budgets': budgets,
                         'r_cap_slopes': r_slopes, 'r_price': rprice}
    L = max(prices)
    # A_T q5+B_T q15 <=qprice*(q5+q15); one exact simplex endpoint maximum.
    residual_price = max(L, qprice/gap)
    upper = finite_upper-record['reference']+record['source_delta_price']*d+residual_price*rho
    return {**record, 'first_beta': first_beta, 'finite_transport': finite_record,
            'coordinate_prices': tuple(prices), 'q_sum_price': qprice,
            'shared_residual_price': residual_price, 'upper': upper}


def shallow_bounds(par):
    require(0 <= par['delta'] <= F(1, 27) and 0 <= par['rho'] <= F(1, 100000),
            'Audited shallow rectangle, both orientations')
    require(6-49*F(1, 27)-70*F(1, 27)**2 > 0 and 42-35*F(1, 27)**2 > 0,
            'Whole-interval positive numerators for Cbar-(1+tbar) and Cbar-kbar')
    rows = [one_label_bound(label, L, par) for L in (2, 3, 4) for label in labels()]
    old = get('uniform_ap_survival_denominator').uniform_H1(par)
    bounded = []
    for previous in old['bounded_labels']:
        m = previous['modulus']
        candidates = [r for r in rows if r['label'][0] == m]
        top = max(r['upper'] for r in candidates)
        distinct = sorted({r['upper'] for r in candidates}, reverse=True)
        bounded.append({'modulus': m, 'face': FACE[m], 'transported_upper': top,
                        'previous_upper': previous['upper'], 'raw_haar_cap': F(1, m),
                        'upper': min(top, previous['upper'], F(1, m)),
                        'maximizers': [{'first_beta': r['first_beta'], 'label': r['label']} for r in candidates if r['upper'] == top],
                        'next_distinct_gap': top-distinct[1] if len(distinct) > 1 else None})
    if par['delta'] == par['rho'] == 0:
        require({r['modulus']: r['upper'] for r in bounded} == FACE, 'Every adopted face cap is recovered exactly')
    return {'bounded_labels': bounded, 'layout_rows': rows, 'layout_count': len(rows)}


def uniform_H1(par):
    old = get('uniform_ap_survival_denominator').uniform_H1(par)
    shallow = shallow_bounds(par)
    positive7 = F(11, 72)+11*par['delta']/36
    upper = (sum(r['upper'] for r in shallow['bounded_labels'])
             +sum(r['upper'] for r in old['complete_exponent_tails'])+old['deep_mixed_upper']+positive7)
    require(upper <= old['upper'], 'Rebuilt positive H1 category sum dominates the previous interface')
    return {'upper': upper, 'face_upper': F(443, 900), 'excess': upper-F(443, 900),
            'bounded_labels': shallow['bounded_labels'], 'complete_exponent_tails': old['complete_exponent_tails'],
            'deep_mixed_upper': old['deep_mixed_upper'], 'complete_positive7_upper': positive7,
            'previous_upper': old['upper'], 'layout_rows': shallow['layout_rows']}


def uniform_square(par):
    return get('uniform_square_and_raw81_neighborhood').uniform_square(
        par, SimpleNamespace(uniform_H1=uniform_H1), get('complete_off_face_factorial_tail'),
        get('complete_off_face_omitted_tails'))


def actual_source_checks(base):
    """Literal height6 residues, then the same disjoint-cylinder formulas at height12."""
    finite, complete = get('finite_source_face_transport'), get('complete_off_face_cost')
    source = module('shallow_actual_source', base/'verify_joint_frontier.py')
    forced, constructor = get('quantitative_forced27'), get('source_mass_compatibility')
    literal = forced.finite_source(constructor, 6)
    A, B = literal['A'], literal['B']
    cell_residues, slots = (0, 3, 1, 4, 7), (1, 2, 3, 0, 4)
    slot_masks = tuple(sum(1 << y for y in range(s, B, 5)) for s in slots)
    literal_X = tuple(F(sum((literal['state'][x] & slot_masks[j]).bit_count()
                            for x in range(cell_residues[c], A, 9)), A*B)
                      for c, j in product(range(5), repeat=2))
    checks = []
    for height, epsilon in ((6, F(0)), (12, F(0)), (12, F(1, 5**7))):
        case = complete.actual_398_case(finite, source, height)
        _, n, eta, _, _ = case['dat']
        z = case['parameter'][4]
        t, qdeleted = case['parameter'][0][0]/9, 1-z
        X = [F(0)]*25
        for c in range(5):
            X[5*c+1] = (eta[c]-t)/5 if c == 0 else eta[c]/5 if c == 1 else F(0)
            X[5*c+2] = F(0) if c == 2 else eta[c]/5
            X[5*c+4] = eta[c]/5
            X[5*c+3] = n[c]-sum(X[5*c:5*c+5])
        if height == 6:
            require(tuple(X) == literal_X, 'Independent literal original-residue matrix equals the disjoint-cylinder formula')
        for c in range(5):
            X[5*c+3] += eta[c]*epsilon
            X[5*c+4] -= eta[c]*epsilon
        qslots = list(case['qslots'])
        qslots[3] += epsilon
        qslots[4] -= epsilon
        h, h1 = sum(eta), sum(eta[2:])
        r, r1 = h*epsilon, h1*epsilon
        point = finite.source_point(case['parameter'], case['pi'], r, 2, r1)
        v7 = F(1, 7**height)
        u7, k7 = (1-v7)/5, (1-v7)/(5+v7)
        df = dict(case['defects'])
        df['E5'] += u7*r
        df['E15'] += u7*r1
        df['omega'] -= (u7-k7)*epsilon
        df['rho'] += k7*epsilon
        delta = F(1, 27) if height == 6 else F(1, 10000)
        par = get('uniform_k_neighborhood_cost').parameters(delta, df['rho'])
        require(case['sigma'] <= delta and min(X) >= 0
                and all(v <= cap for v, cap in zip(X, point['caps'])), 'One actual source obeys its original caps')
        require(tuple(sum(X[5*c:5*c+5]) for c in range(5)) == n, 'All actual row masses retained')
        require(sum(X[5*c+4] for c in range(5)) == h/5-r
                and sum(X[5*c+4] for c in (2, 3, 4)) == h1/5-r1, 'Both DP14 equalities hold on the same actual matrix')
        E27 = case['E27']
        y = (df['E5']-par['gap']*case['q'][0], df['E15']-par['gap']*case['q'][1],
             E27, df['E3']-E27, df['E5d'], df['E15d'], df['omega'])
        require(min(y) >= 0 and y[0] >= r/5 and y[1] >= r1/5
                and sum(y) <= df['rho']-par['gap']*sum(case['q']), 'All seven actual defects share exactly one shifted budget')
        face = face_point(2)
        wq = finite.weights(point, case['q'])
        wface = finite.weights(face, (F(0), F(0)))
        require(all(a-b <= delta*F(int(i//5 != 0), 5)
                    +case['q'][0]*int(i % 5 == 4)+case['q'][1]*int(i//5 >= 2 and i % 5 == 4)
                    for i, (a, b) in enumerate(zip(wq, wface))), 'Actual common-carrier coefficient movement')
        minimum_credit, minimum_reference, minimum_transport = None, None, None
        for label in labels():
            phi = indicator(label)
            rec = indicator_prices(label, par)
            actual_ref = reference(label, eta, qslots)['total']
            source_error = rec['source_discrepancy_price']*(z-max(point['d']))
            extra = (u7*t*sum(qslots[j]*phi[5+j] for j in range(5))
                     +u7*(qdeleted-F(1, 5))*sum(eta[c]*(1+ROOT[c])*phi[5*c+3] for c in range(5)))
            cp = rec['coordinate_prices_before_finite_transport']
            lower = actual_ref-source_error-sum(a*b for a, b in zip(cp[2:6], y[2:6]))
            credit_slack = extra-lower
            reference_slack = (rec['source_delta_price']*delta+rec['slot_migration_price']*y[0]
                               -(rec['reference']-actual_ref+source_error))
            bound = one_label_bound(label, 2, par)
            # This actual retained source expression still upper-bounds survivor mass;
            # other virtual deletion families have only been dropped.
            observed = sum(a*b*c for a, b, c in zip(wq, phi, X))-extra+df['omega']
            transport_slack = bound['upper']-observed
            require(min(credit_slack, reference_slack, transport_slack) >= 0,
                    'Actual original indicator credit, signed migration, and complete transported bound')
            minimum_credit = credit_slack if minimum_credit is None else min(minimum_credit, credit_slack)
            minimum_reference = reference_slack if minimum_reference is None else min(minimum_reference, reference_slack)
            minimum_transport = transport_slack if minimum_transport is None else min(minimum_transport, transport_slack)
        checks.append({'height': height, 'pure5_migration': epsilon, 'sigma': case['sigma'],
                       'rho': df['rho'], 'matrix': X, 'DP14_H_masses': (h/5-r, h1/5-r1),
                       'shifted_defects': y, 'indicators': 47, 'minimum_credit_slack': minimum_credit,
                       'minimum_reference_slack': minimum_reference, 'minimum_transport_slack': minimum_transport,
                       'within_exported_residual_radius': df['rho'] <= F(1, 100000)})
    require(checks[2]['within_exported_residual_radius'], 'A genuine nonzero H/Q migration lies inside the exported small rectangle')
    return {'literal_source_height': 6, 'literal_period': A*B, 'actual_cases': checks,
            'scope': 'Finite checks of actual source identities and single-indicator transport. The height6 residual is separately reported; continuum validity uses the ordinary inequalities, not finite fixtures.'}


def calculate(base):
    io = module('shallow_io', base/'certificate_io.py')
    pins = dict(PINS)
    for name in ('uniform_k_neighborhood_cost', 'uniform_ap_survival_denominator',
                 'uniform_square_and_raw81_neighborhood', 'finite_source_face_transport'):
        for p, h in get(name).PINS.items():
            require(p not in pins or pins[p] == h, 'Consistent inherited source binding '+p)
            pins[p] = h
    for p, h in pins.items():
        require(sha256(io.read_artifact_bytes(base/p)).hexdigest() == h, 'Pinned input '+p)
    audit = face_audit()
    rows = []
    for delta, rho in ((F(0), F(0)), (F(1, 10000), F(1, 100000)),
                       (F(1, 50), F(1, 100000)), (F(1, 27), F(1, 100000))):
        par = get('uniform_k_neighborhood_cost').parameters(delta, rho)
        H1, square = uniform_H1(par), uniform_square(par)
        old_square = get('uniform_square_and_raw81_neighborhood').uniform_square(
            par, get('uniform_ap_survival_denominator'), get('complete_off_face_factorial_tail'),
            get('complete_off_face_omitted_tails'))
        require(square['full_square_upper'] <= old_square['full_square_upper'], 'Direct positive LCM reconstruction improves the old square')
        rows.append({'parameters': par, 'H1': H1, 'square': square, 'previous_square_upper': old_square['full_square_upper']})
        print('delta='+str(delta)+' H1='+str(float(H1['upper']))+' Q='+str(float(square['full_square_upper'])), flush=True)
    return get('uniform_k_neighborhood_cost').encode({
        'schema': 'erdos7-uniform-shallow-indicator-transport-v1', 'source_sha256': pins,
        'face_audit': audit, 'actual_source_checks': actual_source_checks(base), 'radius_results': rows,
        'scope': 'Ordinary independent-cylinder transport using the actual simultaneous DP14 identities, frozen source-only capacity duals and one actual residual. All47 independent shallow layouts and3 first-beta cells; complete H1 and positive weighted LCM tails. No new global K, actual relaxation attainment, Lean or unrestricted Erdos7 claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('shallow_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact independent shallow certificate')
    print('PASS: all independent shallow caps and complete H1/LCM inputs.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
