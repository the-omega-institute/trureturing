"""Six original linear tests share the actual survival-carrier mixture.

The six unchanged global barriers retain each test's own100 source layouts.
At profile39's six refined vertices, replace the already refined six margins;
elsewhere replace their old one-event margins. The other35 tests retain their
existing lower bounds. Tables are lower bounds for the globally separately
concave comparison, not asserted to be concave themselves.
"""
from fractions import Fraction as F
from itertools import product
from hashlib import sha256

SIX = (0, 1, 7, 16, 17, 23)
CARRIERS = tuple(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4)))
Q = F(23, 42)
CAPS = ((11, F(5, 3)), (13, F(12, 7)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def direction(experiment, index, ci, dat):
    """Rebuild old/new independent margins and all18 conditioned margins."""
    E, source = experiment, experiment.source
    d, n, eta, s, _ = dat
    spec = E.specs[ci]
    C = F(E.thresholds[ci]['constant'])
    zero, tag = spec['zero'], spec['tag']
    common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
    positives = E.positive(ci, eta)
    old_positive = source.zero5_positive_with_constant(zero, eta)
    best, old_min, new_min = [None]*18, None, None
    for item in spec['layouts']:
        b = item['baseline']
        k, unit = item['joint']
        require(k == tuple(C-source.zero5_cost(tag, v) for v in b), 'Unchanged cofactor cost')
        base = common+sum(n[j]*item['psi'][j]+eta[j]*item['correction'][j] for j in range(5))
        base += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
        old_cap = E.fixed._cofactor_cap(dat, k, unit, 5)
        old = C*s-base-old_positive-old_cap/5
        require(old >= 0, 'Original nonnegative six-direction margin')
        old_min = old if old_min is None else min(old_min, old)
        kw = tuple(9*eta[j]*k[j] for j in range(5))
        last = F(1, 486)*max(k[j]*d[j] for j in range(5))
        last += (sum(kw)+max(sum(kw[:2]), sum(kw[2:]))+max(kw))/36+max(k)/72
        for li, c5 in enumerate(source.BASES):
            correction = tuple(v*t for v, t in zip(unit, c5))
            require(all(0 <= u <= v <= kk for u, v, kk in zip(unit, correction, k)),
                    'Global barrier pays the three original event floors')
            signed = tuple(k[j]*n[j]-correction[j]*eta[j]/5 for j in range(5))
            deep = tuple(k[j]*d[j]-correction[j]/5 for j in range(5))
            require(all(v >= kk/20 >= 0 for v, kk in zip(deep, k)), 'Nonnegative deep cofactor remainder')
            rest = F(13, 243)*max(deep)+last
            root, cell = (F(0), sum(signed[:2]), sum(signed[2:])), (F(0),)+signed
            cap = max(root)+max(cell)+rest
            require(cap == E.linear.event_cap(dat, k, correction) and cap <= old_cap,
                    'Conditional cap reconstructs the new cap and improves the inherited cap')
            center = C*s-base-positives[li]-rest/5
            actual = C*s-base-positives[li]-cap/5
            require(actual >= old, 'Every refined layout dominates its inherited baseline')
            new_min = actual if new_min is None else min(new_min, actual)
            for ri, r in enumerate(root):
                for ji, c in enumerate(cell):
                    pos, value = 6*ri+ji, center-(r+c)/5
                    best[pos] = value if best[pos] is None else min(best[pos], value)
    require(min(best) == new_min >= old_min, 'All18 margins reconstruct the true independent margin')
    inherited = new_min if index in E.changes else old_min
    if index in E.changes:
        known = E.changes[index]['directions'][ci]
        require((old_min, new_min) == (F(known['old_margin']), F(known['new_margin'])),
                'Old and refined selected-vertex margins both match profile39')
    return {'index': ci, 'weight': E.weights[ci], 'old_min': old_min,
            'new_min': new_min, 'inherited_min': inherited, 'conditional': best}


def reconstruct(experiment, rows46, progress=None):
    E, source = experiment, experiment.source
    require(len(rows46) == 1296 and [r['index'] for r in rows46] == list(range(1296)),
            'Complete reconstructed46 source domain')
    require(tuple((E.specs[i]['name'], tuple(E.specs[i]['tuple'])) for i in SIX)
            == E.linear.UNCHANGED_BARRIERS[:6], 'Exactly the six unchanged R17/R19 barriers')
    require(all(F(E.thresholds[i]['increase']) == 0 for i in SIX), 'Six zero barrier increases')
    records, controls, result, gains, joint_gains = [], [], [], [], []
    digest = sha256()
    for index, old in enumerate(rows46):
        dat = source.data(E.parameters[index])
        require((old['s'], old['D']) == dat[3:], 'Same actual source parameter')
        directions = [direction(E, index, ci, dat) for ci in SIX]
        base = old['M41']-sum(r['weight']*r['inherited_min'] for r in directions)
        independent = base+sum(r['weight']*r['new_min'] for r in directions)
        conditional = [base+sum(r['weight']*r['conditional'][j] for r in directions) for j in range(18)]
        require(min(conditional) >= independent >= old['M41'], 'Safe independent and joint replacements')
        require(all(tuple(c['carrier']) == CARRIERS[j] for j, c in enumerate(old['conditional'])),
                'Exactly the same18 carriers as survival and mass')
        gain, joint_gain = independent-old['M41'], min(conditional)-independent
        gains.append(gain)
        joint_gains.append(joint_gain)
        for r in directions:
            for j, value in enumerate(r['conditional']):
                digest.update(f"{index},{r['index']},{CARRIERS[j]}:{value}\n".encode())
        updated = dict(old)
        updated['independent_M41'] = independent
        updated['conditional_M41'] = conditional
        result.append(updated)
        records.append({'index': index, 'independent_gain': gain, 'joint_minimum_gain': joint_gain,
                        'independent_M41': independent, 'conditional_M41': conditional})
        if index in (398, 402):
            controls.append({'index': index, 'directions': directions})
        if progress is not None:
            progress(index+1, 1296)
    require(all(gains[i] == 0 for i in E.changes), 'No selected-vertex double counting')
    return result, {'directions': [{'index': i, 'name': E.specs[i]['name'], 'tuple': E.specs[i]['tuple'],
                                   'weight': E.weights[i], 'constant': F(E.thresholds[i]['constant'])}
                                  for i in SIX],
                    'carriers': CARRIERS, 'source_vertices': 1296, 'refined_predecessor_vertices': list(E.changes),
                    'old_layout_checks': 77760, 'new_layout_checks': 777600,
                    'conditional_layout_checks': 13996800, 'conditional_margin_values': 139968,
                    'selected_old_and_new_margin_checks': 72,
                    'positive_independent_gain_vertices': sum(g > 0 for g in gains),
                    'minimum_independent_gain': min(gains), 'maximum_independent_gain': max(gains),
                    'positive_joint_minimum_gain_vertices': sum(g > 0 for g in joint_gains),
                    'maximum_joint_minimum_gain': max(joint_gains),
                    'rows': records, 'control_directions': controls, 'conditional_margin_sha256': digest.hexdigest(),
                    'scope': 'Six independently labelled source tests share the survival-carrier mixture. At six previously refined vertices replace their new independent margins; elsewhere replace their old one-event margins. Other35 costs keep existing lower bounds. All source and cofactor tails remain complete.'}


def consume(source, core, kc, previous46, pure, rows):
    keys = ('bound', 'Gamma13', 'T13_81', 'combined')
    modes = ('previous46', 'independent_six', 'joint_six')
    H16, H41, A81, cG = (F(previous46[k]) for k in ('H16', 'H41', 'A81', 'cG'))
    H = source.AC*H16+H41
    slopes = {'bound': H, 'Gamma13': H16, 'T13_81': A81, 'combined': H+A81}
    offsets = {'bound': source.WHOLE_CONST, 'Gamma13': F(16), 'T13_81': F(0), 'combined': source.WHOLE_CONST}
    targets = {mode: {k: None for k in keys} for mode in modes}
    choices = {mode: {k: [] for k in keys} for mode in modes}
    rho, rho_choices, prepared = None, [], []
    finite, tails = source.ap_product_distribution(CAPS, 9)
    require(cG == tails[2]+sum(k*k*finite[k] for k in (7, 8)), 'Complete unchanged square-tail coefficient')
    parameters, denominator_checks = list(source.vertices()), 0
    for row in rows:
        index, s = row['index'], row['s']
        dat = source.data(parameters[index])
        mg, mq = row['source_margin'], row['Mquad']
        raw81 = sum(prob*n*n*source.square357(F(81, n*n), dat) for n, prob in finite.items() if n < 7)
        for j, cond in enumerate(row['conditional']):
            low, M = cond['D_c'], cond['M']
            linear = {'previous46': row['M41'], 'independent_six': row['independent_M41'],
                      'joint_six': row['conditional_M41'][j]}
            corrections = {mode: {'bound': source.AC*mq+ml, 'Gamma13': mq, 'T13_81': cG*mg-raw81,
                                  'combined': source.AC*mq+ml+cG*mg-raw81} for mode, ml in linear.items()}
            prepared.append((index, CARRIERS[j], low, s, M, corrections))
            for endpoint, X in (('D_c', low), ('s', s)):
                delta = Q*X+M
                require(delta > 0, 'Both actual-mass endpoint denominators are positive')
                denominator_checks += 1
                label = [index, CARRIERS[j], endpoint]
                for mode in modes:
                    for k in keys:
                        numerator = slopes[k]*X-corrections[mode][k]
                        require(numerator > 0, 'Positive numerator at each actual-mass endpoint')
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
    require(all(targets['previous46'][k] == F(previous46[k]) for k in keys)
            and rho == F(previous46['rho']), 'All five published46 targets independently recovered')
    results = {}
    for mode in modes[1:]:
        current = targets[mode]
        require(all(current[k] == F(previous46[k]) for k in ('Gamma13', 'T13_81')),
                'Unchanged Gamma13 and T81 targets')
        require(all(current[k] < F(previous46[k]) for k in ('bound', 'combined')),
                'Both source targets strictly improve46')
        coefficients = {k: Q*(current[k]-offsets[k])-slopes[k] for k in keys}
        coefficients['rho'] = Q-rho
        minima = {k: None for k in coefficients}
        digest, count, selected_count = sha256(), 0, 0
        for index, carrier, low, s, M, corrections in prepared:
            for endpoint, X in (('D_c', low), ('s', s)):
                for k, coefficient in coefficients.items():
                    margin = coefficient*X+M if k == 'rho' else (
                        coefficient*X+(current[k]-offsets[k])*M+corrections[mode][k])
                    require(margin >= 0, 'Every signed fixed-target endpoint inequality')
                    count += 1
                    if endpoint == ('D_c' if coefficient >= 0 else 's'):
                        minima[k] = margin if minima[k] is None else min(minima[k], margin)
                        digest.update(f'{index},{carrier},{k},{endpoint}:{margin}\n'.encode())
                        selected_count += 1
        branches, full_rho = core.fallbacks(source, CAPS, F(previous46['source_G357']),
                                          {k: current[k] for k in keys if k != 'combined'}, rho)
        require(full_rho == rho and len(branches) == 8, 'All eight fallback targets and survival')
        for branch in branches:
            branch['combined_bound'] = branch['bound']+branch['T13_81']
            branch['combined_margin'] = current['combined']-branch['combined_bound']
            require(branch['combined_margin'] > 0, 'Every fallback combined target')
        inputs, errors = core.core_errors(kc, pure['source_inputs'], current['Gamma13'], rho,
                                         current['T13_81'], current['bound'])
        gain = current['bound']+current['T13_81']-current['combined']
        require(gain >= 0, 'Common-law target sum dominates joint target')
        for error in errors:
            error['combined_gap'] = current['combined']+error['total']-403
            require(error['combined_gap'] == error['gap']-gain, 'Complete-core gap interface')
        require(count == 233280 and selected_count == 116640 and len(errors) == 2,
                'All source/carrier/target endpoints and complete cores')
        results[mode] = {**current, 'rho': rho, 'coefficients': coefficients,
                         'selected_mass_endpoints': {k: 'D_c' if a >= 0 else 's' for k, a in coefficients.items()},
                         'minimum_margins': minima, 'combined_target_gain': gain,
                         'controllers': choices[mode] | {'rho': rho_choices},
                         'maximizers': {k: sorted({v[0] for v in choices[mode][k]}) for k in keys},
                         'rho_minimizers': sorted({v[0] for v in rho_choices}),
                         'source_inputs': inputs, 'fallbacks': branches, 'core_errors': errors,
                         'consumer_vertex_checks': 1296, 'consumer_carrier_checks': 23328,
                         'consumer_denominator_checks': denominator_checks,
                         'consumer_target_margin_checks': selected_count, 'consumer_endpoint_margin_checks': count,
                         'fallback_checks': 8, 'complete_core_checks': 2, 'consumer_margin_sha256': digest.hexdigest()}
    independent, joint = results['independent_six'], results['joint_six']
    require(denominator_checks == 46656 and all(joint[k] < independent[k] for k in ('bound', 'combined')),
            'Strict additional common-carrier improvement at both source targets')
    return joint | {'q_effective': Q, 'H16': H16, 'H41': H41, 'cG': cG, 'A81': A81,
                    'source_G357': F(previous46['source_G357']),
                    'source_comparison_barrier': F(previous46['source_comparison_barrier']),
                    'gain_from46': {k: F(previous46[k])-joint[k] for k in ('bound', 'combined')},
                    'independent_gain_from46': {k: F(previous46[k])-independent[k] for k in ('bound', 'combined')},
                    'additional_common_carrier_gain': {k: independent[k]-joint[k] for k in ('bound', 'combined')},
                    'independent_six': {k: independent[k] for k in ('bound', 'combined', 'coefficients', 'controllers',
                        'minimum_margins', 'consumer_margin_sha256', 'core_errors')},
                    'independent_six_endpoint_checks': independent['consumer_endpoint_margin_checks'],
                    'scope': 'Six original linear tests share one forbidden-carrier mixture with the three survival hinges and actual mass. Independent-six refinement and additional common-carrier gain are accounted separately. Ordinary proof and exact arithmetic; unrestricted Erdos7 remains open.'}
