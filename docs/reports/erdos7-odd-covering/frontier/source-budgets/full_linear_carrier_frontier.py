"""Refine24 frontier vertices for the true41-linear/five-quadratic carrier functions.

Every original test retains its own100 layouts. Other1272 vertices retain
profile47 lower bounds for these globally defined separately concave functions.
No concavity of the patched table or actual-family attainment is asserted.
"""
from fractions import Fraction as F
from itertools import product
from hashlib import sha256

CARRIERS = tuple(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4)))
SELECTED = (398, 402, 404, 406, 410, 414, 416, 418, 422, 426, 428, 430,
            616, 618, 620, 622, 628, 630, 632, 634, 640, 642, 644, 646)
CAPS, Q = ((11, F(5, 3)), (13, F(12, 7))), F(23, 42)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def conditional(E, dat, C, branches, count):
    d, n, eta, s, _ = dat
    selected, tail = (F(13, 243), F(1, 486)) if count == 5 else (F(40, 729), F(1, 1458))
    require(count in (5, 6) and len(branches) == 100, 'Exact independent original layout inventory')
    best, independent = [None]*18, None
    for U, costs, correction in branches:
        k = tuple(C-v for v in costs)
        require(all(0 <= v <= kk for v, kk in zip(correction, k)), 'Fixed barrier pays original event floors')
        a = tuple(k[j]*n[j]-correction[j]*eta[j]/5 for j in range(5))
        z = tuple(k[j]*d[j]-correction[j]/5 for j in range(5))
        require(all(v >= kk/20 >= 0 for v, kk in zip(z, k)), 'Nonnegative deep cofactor remainder')
        w = tuple(9*eta[j]*k[j] for j in range(5))
        rest = selected*max(z)+tail*max(k[j]*d[j] for j in range(5))
        rest += (sum(w)+max(sum(w[:2]), sum(w[2:]))+max(w))/36+max(k)/72
        roots, cells = (F(0), sum(a[:2]), sum(a[2:])), (F(0),)+a
        cap = max(roots)+max(cells)+rest
        known = E.linear.event_cap(dat, k, correction) if count == 5 else E.fixed._cofactor_cap(dat, k, correction, 6)
        require(cap == known, 'Complete unconditioned cap recovered with empty carriers')
        value = C*s-U-cap/5
        independent = value if independent is None else min(independent, value)
        center = C*s-U-rest/5
        for ri, root in enumerate(roots):
            for ji, cell in enumerate(cells):
                pos, margin = 6*ri+ji, center-(root+cell)/5
                best[pos] = margin if best[pos] is None else min(best[pos], margin)
    require(min(best) == independent, 'All18 conditioned minima recover the independent margin')
    return independent, best


def linear_direction(E, dat, ci):
    source, spec = E.source, E.specs[ci]
    d, n, eta, _, _ = dat
    C, zero, tag = F(E.thresholds[ci]['constant']), spec['zero'], spec['tag']
    common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
    positive, branches = E.positive(ci, eta), []
    for item in spec['layouts']:
        b, unit = item['baseline'], item['joint'][1]
        costs = tuple(source.zero5_cost(tag, v) for v in b)
        base = common+sum(n[j]*item['psi'][j]+eta[j]*item['correction'][j] for j in range(5))
        base += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
        for li, c5 in enumerate(source.BASES):
            branches.append((base+positive[li], costs, tuple(v*t for v, t in zip(unit, c5))))
    independent, margins = conditional(E, dat, C, branches, 5)
    return {'index': ci, 'name': spec['name'], 'tuple': spec['tuple'], 'constant': C,
            'weight': E.weights[ci], 'independent_margin': independent, 'conditional': margins}


def quadratic_direction(E, dat, ci):
    source, spec = E.source, E.quadratic_specs[ci]
    d, n, eta, _, _ = dat
    C, tag = E.quadratic_constants[ci], spec['tag']
    zero, psi, curve, _, _ = E.psis[ci]
    common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
    positive, branches = E.quadratic_positive(ci, eta), []
    for b in source.BASES:
        costs = tuple(source.zero5_cost(tag, v) for v in b)
        increments = tuple(source.zero5_cost(tag, v+1)-source.zero5_cost(tag, v) for v in b)
        base = common+sum(n[j]*psi(b[j])+eta[j]*source.zero5_centered_correction(zero, b[j]) for j in range(5))
        base += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
        for li, c5 in enumerate(source.BASES):
            U = base+positive[li]-F(4, 25)*curve*E.distance(eta, b, c5)
            branches.append((U, costs, tuple(v*t for v, t in zip(increments, c5))))
    independent, margins = conditional(E, dat, C, branches, 6)
    return {'index': ci, 'tuple': E.pairs[ci], 'constant': C,
            'independent_margin': independent, 'conditional': margins}


def reconstruct(E, previous47, rows47, progress=None):
    require(len(rows47) == 1296 and [r['index'] for r in rows47] == list(range(1296)), 'Complete47 source domain')
    require(tuple(sorted(set(E.changes) | {r[0] for r in previous47['controllers']['combined']})) == SELECTED,
            'Exactly six previous refined and eighteen combined-control vertices')
    known_six = {r['index']: r['directions'] for r in previous47['six_linear']['control_directions']}
    result, records, digest = [dict(r) for r in rows47], [], sha256()
    for position, index in enumerate(SELECTED):
        old, dat = rows47[index], E.source.data(E.parameters[index])
        require((old['s'], old['D']) == dat[3:], 'Same actual source parameter')
        linear = [linear_direction(E, dat, ci) for ci in range(41)]
        quadratic = [quadratic_direction(E, dat, ci) for ci in range(5)]
        ml = [sum(r['weight']*r['conditional'][j] for r in linear) for j in range(18)]
        independent = sum(r['weight']*r['independent_margin'] for r in linear)
        require(all(a >= b for a, b in zip(ml, old['conditional_M41'])), 'All41 margins dominate47 vertex lower bounds')
        if index in E.changes:
            require(all(r['independent_margin'] == F(E.changes[index]['directions'][r['index']]['new_margin'])
                        for r in linear) and independent == old['M41'], 'All41 old refined independent values recovered')
        else:
            require(independent >= old['independent_M41'], 'Other35 true independent margins dominate inherited bounds')
        if index in known_six:
            for known in known_six[index]:
                actual = linear[known['index']]
                require(actual['independent_margin'] == F(known['new_min'])
                        and actual['conditional'] == [F(v) for v in known['conditional']],
                        'Existing six conditional control directions recovered exactly')
        require([r['independent_margin'] for r in quadratic] == old['quadratic_margins'],
                'All five exact old quadratic contributions recovered before replacement')
        complement = old['Mquad']-sum(old['quadratic_margins'])
        require(complement == E.outside*old['source_margin'], 'Unchanged independent square complement')
        mq = [complement+sum(r['conditional'][j] for r in quadratic) for j in range(18)]
        require(min(mq) >= old['Mquad'], 'All conditioned quadratic aggregates dominate old bounds')
        result[index]['frontier_M41'], result[index]['frontier_Mquad'] = ml, mq
        for kind, directions in (('linear', linear), ('quadratic', quadratic)):
            for r in directions:
                for c, value in zip(CARRIERS, r['conditional']):
                    digest.update(f"{index},{kind},{r['index']},{c}:{value}\n".encode())
        records.append({'index': index, 'old_M41': old['M41'], 'independent_six_M41': old['independent_M41'],
                        'true_independent_M41': independent, 'independent35_gain': independent-old['independent_M41'],
                        'old_conditional_M41': old['conditional_M41'], 'conditional_M41': ml,
                        'old_Mquad': old['Mquad'], 'conditional_Mquad': mq,
                        'linear_directions': linear, 'quadratic_directions': quadratic})
        if progress is not None:
            progress(position+1, len(SELECTED))
    witness = next(r for r in records if r['index'] == 402)
    ca = CARRIERS.index((0, 1))
    require(all(r['independent_margin'] == r['conditional'][ca] == 0 for r in witness['quadratic_directions']),
            'All five quadratic-only margins stay zero at the old402/A control')
    return result, {'carriers': CARRIERS, 'refined_vertices': SELECTED, 'inherited_vertices': 1272,
                    'linear_directions': 41, 'quadratic_directions': 5, 'source_square_conditioned': False,
                    'original_layout_checks': 110400, 'conditional_layout_checks': 1987200,
                    'conditional_margin_values': 19872, 'recovered_selected_linear_values': 246,
                    'recovered_old_quadratic_values': 120, 'rows': records,
                    'conditional_margin_sha256': digest.hexdigest(),
                    'scope': 'True41-linear and five-quadratic conditional functions at24 vertices, with profile47 lower bounds at all other1272 vertices. Each test retains independent source layouts and complete tails. No actual-source feasibility cut and no concavity claim about the patched table.'}


def consume(source, core, kc, previous47, pure, rows):
    keys, modes = ('bound', 'Gamma13', 'T13_81', 'combined'), ('previous47', 'linear_only', 'linear_quad')
    H16, H41, A81, cG = (F(previous47[k]) for k in ('H16', 'H41', 'A81', 'cG'))
    H = source.AC*H16+H41
    slopes = {'bound': H, 'Gamma13': H16, 'T13_81': A81, 'combined': H+A81}
    offsets = {'bound': source.WHOLE_CONST, 'Gamma13': F(16), 'T13_81': F(0), 'combined': source.WHOLE_CONST}
    targets = {mode: {k: None for k in keys} for mode in modes}
    choices = {mode: {k: [] for k in keys} for mode in modes}
    rho, rho_choices, prepared, stopping = None, [], [], None
    finite, tails = source.ap_product_distribution(CAPS, 9)
    require(cG == tails[2]+sum(k*k*finite[k] for k in (7, 8)), 'Complete unchanged square-tail coefficient')
    parameters, denominator_checks = list(source.vertices()), 0
    for row in rows:
        index, s, mg, oldmq = row['index'], row['s'], row['source_margin'], row['Mquad']
        dat = source.data(parameters[index])
        raw81 = sum(prob*n*n*source.square357(F(81, n*n), dat) for n, prob in finite.items() if n < 7)
        for j, cond in enumerate(row['conditional']):
            require(tuple(cond['carrier']) == CARRIERS[j], 'Identical common carrier order')
            oldml = row['conditional_M41'][j]
            ml, mq = row.get('frontier_M41', row['conditional_M41'])[j], row.get('frontier_Mquad', [oldmq]*18)[j]
            lin, quad = {'previous47': oldml, 'linear_only': ml, 'linear_quad': ml}, {'previous47': oldmq, 'linear_only': oldmq, 'linear_quad': mq}
            corr = {m: {'bound': source.AC*quad[m]+lin[m], 'Gamma13': quad[m], 'T13_81': cG*mg-raw81,
                        'combined': source.AC*quad[m]+lin[m]+cG*mg-raw81} for m in modes}
            low, M = cond['D_c'], cond['M']
            prepared.append((index, CARRIERS[j], low, s, M, corr))
            for endpoint, X in (('D_c', low), ('s', s)):
                delta = Q*X+M
                require(delta > 0, 'Positive actual-mass endpoint survival')
                denominator_checks += 1
                label = [index, CARRIERS[j], endpoint]
                for mode in modes:
                    for k in keys:
                        numerator = slopes[k]*X-corr[mode][k]
                        require(numerator > 0, 'Positive conditioned numerator at both mass endpoints')
                        value = offsets[k]+numerator/delta
                        if targets[mode][k] is None or value > targets[mode][k]:
                            targets[mode][k], choices[mode][k] = value, [label]
                        elif value == targets[mode][k]:
                            choices[mode][k].append(label)
                value = delta/X
                if rho is None or value < rho:
                    rho, rho_choices = value, [label]
                elif value == rho:
                    rho_choices.append(label)
                if index == 402 and CARRIERS[j] == (0, 1) and endpoint == 'D_c':
                    require(mq == oldmq, 'Quadratic conditioning alone leaves402/A unchanged')
                    stopping = {k: offsets[k]+(slopes[k]*X-corr['previous47'][k])/delta
                                for k in ('bound', 'Gamma13', 'combined')}
    require(all(targets['previous47'][k] == F(previous47[k]) for k in keys)
            and rho == F(previous47['rho']), 'All five preceding47 targets recovered')
    require(stopping is not None and all(v == F(previous47[k]) for k, v in stopping.items()),
            'Exact retained old control proves quadratic-alone zero target gain')
    results = {}
    for mode in modes[1:]:
        current = targets[mode]
        require(all(current[k] == F(previous47[k]) for k in ('Gamma13', 'T13_81')),
                'Unchanged Gamma13 and T81 targets')
        coeff = {k: Q*(current[k]-offsets[k])-slopes[k] for k in keys}
        coeff['rho'] = Q-rho
        minima, digest, count, selected_count = {k: None for k in coeff}, sha256(), 0, 0
        for index, carrier, low, s, M, corrections in prepared:
            for endpoint, X in (('D_c', low), ('s', s)):
                for k, a in coeff.items():
                    margin = a*X+M if k == 'rho' else a*X+(current[k]-offsets[k])*M+corrections[mode][k]
                    require(margin >= 0, 'Every signed fixed-target endpoint inequality')
                    count += 1
                    if endpoint == ('D_c' if a >= 0 else 's'):
                        minima[k] = margin if minima[k] is None else min(minima[k], margin)
                        digest.update(f'{index},{carrier},{k},{endpoint}:{margin}\n'.encode())
                        selected_count += 1
        branches, full_rho = core.fallbacks(source, CAPS, F(previous47['source_G357']),
                                          {k: current[k] for k in keys if k != 'combined'}, rho)
        require(full_rho == rho and len(branches) == 8, 'Complete eight fallback branches')
        for branch in branches:
            branch['combined_bound'] = branch['bound']+branch['T13_81']
            branch['combined_margin'] = current['combined']-branch['combined_bound']
            require(branch['combined_margin'] > 0, 'Every fallback combined target')
        inputs, errors = core.core_errors(kc, pure['source_inputs'], current['Gamma13'], rho, current['T13_81'], current['bound'])
        gain = current['bound']+current['T13_81']-current['combined']
        require(gain >= 0, 'Combined target dominates the sum of separate comparisons')
        for error in errors:
            error['combined_gap'] = current['combined']+error['total']-403
            require(error['combined_gap'] == error['gap']-gain, 'Same complete-core interface')
        require(count == 233280 and selected_count == 116640 and len(errors) == 2, 'Complete vertex/carrier/target and core inventory')
        results[mode] = {**current, 'rho': rho, 'coefficients': coeff,
                         'selected_mass_endpoints': {k: 'D_c' if a >= 0 else 's' for k, a in coeff.items()},
                         'minimum_margins': minima, 'combined_target_gain': gain,
                         'controllers': choices[mode] | {'rho': rho_choices},
                         'maximizers': {k: sorted({v[0] for v in choices[mode][k]}) for k in keys},
                         'rho_minimizers': sorted({v[0] for v in rho_choices}), 'source_inputs': inputs,
                         'fallbacks': branches, 'core_errors': errors, 'consumer_vertex_checks': 1296,
                         'consumer_carrier_checks': 23328, 'consumer_denominator_checks': denominator_checks,
                         'consumer_target_margin_checks': selected_count, 'consumer_endpoint_margin_checks': count,
                         'fallback_checks': 8, 'complete_core_checks': 2, 'consumer_margin_sha256': digest.hexdigest()}
    linear, joint = results['linear_only'], results['linear_quad']
    require(denominator_checks == 46656 and linear['combined'] < F(previous47['combined'])
            and joint['combined'] < linear['combined'] and joint['bound'] == linear['bound'] < F(previous47['bound']),
            'Both genuine improvement stages with fixed barriers')
    require(linear['maximizers']['combined'] == [398, 410, 422, 616, 628, 640]
            and joint['maximizers']['combined'] == [402, 404, 406, 414, 416, 418, 426, 428, 430,
                                                   618, 620, 622, 630, 632, 634, 642, 644, 646],
            'Complete individually evaluated control inventories')
    return joint | {'q_effective': Q, 'H16': H16, 'H41': H41, 'cG': cG, 'A81': A81,
                    'source_G357': F(previous47['source_G357']), 'source_comparison_barrier': F(previous47['source_comparison_barrier']),
                    'gain_from47': {k: F(previous47[k])-joint[k] for k in keys},
                    'linear_gain_from47': {k: F(previous47[k])-linear[k] for k in keys},
                    'additional_quadratic_gain': {k: linear[k]-joint[k] for k in keys},
                    'quadratic_alone_stopping': {'index': 402, 'carrier': (0, 1), 'endpoint': 'D_c', 'unchanged_targets': stopping},
                    'linear_only': {k: linear[k] for k in ('bound', 'combined', 'coefficients', 'controllers', 'minimum_margins',
                                                         'consumer_margin_sha256', 'core_errors')},
                    'linear_only_endpoint_checks': linear['consumer_endpoint_margin_checks'],
                    'scope': 'One global41-linear/five-quadratic carrier function;24 true vertex refinements and1272 retained47 lower bounds. Independent square complement, fixed barriers, same actual mass and complete tails. No actual-source cut, no asserted extremal covering family, and unrestricted Erdos7 remains open.'}
