"""Consume whole-hinge margins on the same actual source-mass interval.

The globally defined true absorbed margins are mathematical inputs. Their
vertex lower bounds are used here without any concavity claim for epsilon.
Both S=D and S=s are evaluated; the fixed-target coefficient then selects
the correct endpoint for the continuous-extension margin.
"""
from fractions import Fraction as F
from hashlib import sha256
import json

Q = F(23, 42)
Q_PREVIOUS = F(193, 231)
CAPS = ((11, F(5, 3)), (13, F(12, 7)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def consume(source, core, kc, encode, previous, pure, rows):
    H16, H41, cG, A81 = (F(previous[k]) for k in ('H16', 'H41', 'cG', 'A81'))
    H = source.AC*H16+H41
    require(F(previous['source_G357']) == F(102715, 2916)
            and F(previous['source_comparison_barrier']) == 45
            and F(previous['q_effective']) == Q_PREVIOUS
            and Q == Q_PREVIOUS-F(1, 6)-F(4, 33),
            'Same proved source norm, square barrier and fully charged survival constants')
    parameters = list(source.vertices())
    require(len(rows) == len(parameters) == 1296
            and [row['index'] for row in rows] == list(range(1296)),
            'Complete ordered actual source-parameter domain')
    finite, tails = source.ap_product_distribution(CAPS, 9)
    require(cG == tails[2]+sum(n*n*finite[n] for n in (7, 8)), 'Complete unchanged AP square-tail coefficient')
    keys = ('bound', 'Gamma13', 'T13_81', 'combined')
    constants = {'bound': source.WHOLE_CONST, 'Gamma13': F(16),
                 'T13_81': F(0), 'combined': source.WHOLE_CONST}
    slopes = {'bound': H, 'Gamma13': H16, 'T13_81': A81, 'combined': H+A81}
    current = []
    old_targets = {key: None for key in keys}
    old_rho = None
    for index, (parameter, row) in enumerate(zip(parameters, rows)):
        dat = source.data(parameter)
        s, D = dat[3:]
        require((row['s'], row['D']) == (s, D) and 0 < D <= s, 'Same raw source mass interval')
        mg, Mq, Ml, m25, m4, m5 = (F(row[k]) for k in
            ('source_margin', 'Mquad', 'M41', 'survival_hinge_margin',
             'absorbed_hinge_4_margin', 'absorbed_hinge_5_margin'))
        e4, e5 = (F(row['absorbed_hinge_'+str(t)+'_epsilon']) for t in (4, 5))
        raw4, raw5 = (source.raw357(F(t), dat) for t in (4, 5))
        require(e4 >= 0 and e5 >= 0 and m4 == D-raw4+e4 and m5 == D-raw5+e5,
                'Both absorbed margins are the exact certified vertex lower bounds')
        Ms = m4/6+F(4, 33)*m5+m25/22
        delta = Q*D+Ms
        old_delta = Q_PREVIOUS*D-raw4/6-F(4, 33)*raw5+m25/22
        require(delta == old_delta+e4/6+F(4, 33)*e5 and old_delta > 0 and delta > 0,
                'Exact raw survival improvement after paying all three constants')
        raw81 = sum(prob*n*n*source.square357(F(81, n*n), dat)
                    for n, prob in finite.items() if n < 7)
        corrections = {'bound': source.AC*Mq+Ml, 'Gamma13': Mq,
                       'T13_81': cG*mg-raw81,
                       'combined': source.AC*Mq+Ml+cG*mg-raw81}
        numerators_D = {key: slopes[key]*D-corrections[key] for key in keys}
        require(min(numerators_D.values()) > 0, 'Positive raw comparison numerators at D')
        endpoint_values = {key: {} for key in keys}
        endpoint_rho, endpoint_delta = {}, {}
        for name, endpoint in (('D', D), ('s', s)):
            denominator = Q*endpoint+Ms
            require(denominator > 0, 'Positive denominator at each actual-mass endpoint')
            endpoint_delta[name] = denominator
            endpoint_rho[name] = denominator/endpoint
            for key in keys:
                numerator = slopes[key]*endpoint-corrections[key]
                require(numerator > 0, 'Positive cost numerator at each actual-mass endpoint')
                endpoint_values[key][name] = constants[key]+numerator/denominator
        for key in keys:
            prior = constants[key]+numerators_D[key]/old_delta
            old_targets[key] = prior if old_targets[key] is None else max(old_targets[key], prior)
        prior_rho = old_delta/D
        old_rho = prior_rho if old_rho is None else min(old_rho, prior_rho)
        current.append({'index': index, 's': s, 'D': D, 'Delta': delta,
                        'survival_margin_sum': Ms, 'source_margin': mg,
                        'Mquad': Mq, 'M41': Ml, 'Raw81': raw81,
                        'survival_hinge_margin': m25, 'absorbed_hinge_4_margin': m4,
                        'absorbed_hinge_5_margin': m5, 'epsilon4': e4, 'epsilon5': e5,
                        'corrections': corrections, 'endpoint_values': endpoint_values,
                        'endpoint_denominators': endpoint_delta, 'endpoint_rho': endpoint_rho})
    require(all(old_targets[k] == F(previous[k]) for k in keys) and old_rho == F(previous['rho']),
            'Published profile41 targets and controlling survival reconstructed')
    targets = {key: max(value for row in current for value in row['endpoint_values'][key].values())
               for key in keys}
    rho = min(value for row in current for value in row['endpoint_rho'].values())
    coefficients = {key: Q*(targets[key]-constants[key])-slopes[key] for key in keys}
    coefficients['rho'] = Q-rho
    require(0 < rho <= 1 and all(targets[k] > constants[k] for k in keys),
            'Positive survival and nonnegative true-margin multipliers')
    selected = {key: ('D' if coefficient >= 0 else 's') for key, coefficient in coefficients.items()}
    digest = sha256()
    minima = {key: None for key in coefficients}
    count = endpoint_count = 0
    for row in current:
        Ms = row['survival_margin_sum']
        for key in keys:
            target = targets[key]-constants[key]
            for name in ('D', 's'):
                X = row[name]
                margin = target*(Q*X+Ms)-slopes[key]*X+row['corrections'][key]
                require(margin == coefficients[key]*X+target*Ms+row['corrections'][key]
                        and isinstance(margin, F) and margin >= 0,
                        'Exact nonnegative endpoint cost target: '+key)
                endpoint_count += 1
                if name == selected[key]:
                    minima[key] = margin if minima[key] is None else min(minima[key], margin)
                    digest.update(f"{row['index']},{key},{name}:{margin}\n".encode())
                    count += 1
        for name in ('D', 's'):
            X = row[name]
            margin = (Q-rho)*X+Ms
            require(margin == row['endpoint_denominators'][name]-rho*X
                    and isinstance(margin, F) and margin >= 0,
                    'Exact nonnegative endpoint survival target')
            endpoint_count += 1
            if name == selected['rho']:
                minima['rho'] = margin if minima['rho'] is None else min(minima['rho'], margin)
                digest.update(f"{row['index']},rho,{name}:{margin}\n".encode())
                count += 1
    branch_targets = {key: targets[key] for key in keys if key != 'combined'}
    branches, total_rho = core.fallbacks(source, CAPS, F(previous['source_G357']), branch_targets, rho)
    require(total_rho == rho, 'All other source branches preserve the reported survival')
    for branch in branches:
        branch['combined_bound'] = branch['bound']+branch['T13_81']
        branch['combined_margin'] = targets['combined']-branch['combined_bound']
        require(branch['combined_margin'] > 0, 'Every complete fallback combined target')
    source_inputs, errors = core.core_errors(kc, pure['source_inputs'], targets['Gamma13'], rho,
                                           targets['T13_81'], targets['bound'])
    combined_gain = targets['bound']+targets['T13_81']-targets['combined']
    require(combined_gain >= 0, 'Common-law sum controlled by the separate maxima')
    for error in errors:
        error['combined_gap'] = targets['combined']+error['total']-403
        require(error['combined_gap'] == error['gap']-combined_gain, 'Same complete-core interface')
    require(count == 6480 and endpoint_count == 12960 and len(branches) == 8 and len(errors) == 2,
            'Both mass endpoints, five final targets, eight fallbacks and both complete cores')
    require(all(targets[key] < F(previous[key]) for key in keys) and rho > F(previous['rho']),
            'All numerator targets and actual survival improve the published profile41 bounds')
    return {**targets, 'rho': rho, 'q_effective': Q,
            'H16': H16, 'H41': H41, 'cG': cG, 'A81': A81,
            'source_G357': F(previous['source_G357']), 'source_comparison_barrier': F(45),
            'coefficients': coefficients, 'selected_mass_endpoints': selected,
            'minimum_margins': minima, 'combined_target_gain': combined_gain,
            'maximizers': {key: [row['index'] for row in current
                                 if max(row['endpoint_values'][key].values()) == targets[key]] for key in keys},
            'maximizer_endpoints': {key: [[row['index'], name] for row in current for name in ('D', 's')
                                        if row['endpoint_values'][key][name] == targets[key]] for key in keys},
            'rho_minimizers': [row['index'] for row in current if min(row['endpoint_rho'].values()) == rho],
            'source_inputs': source_inputs, 'fallbacks': branches, 'core_errors': errors,
            'consumer_vertex_checks': 1296, 'consumer_target_margin_checks': count,
            'consumer_endpoint_margin_checks': endpoint_count,
            'fallback_checks': 8, 'complete_core_checks': 2,
            'consumer_margin_sha256': digest.hexdigest(),
            'row_sha256': sha256(json.dumps(encode(current), sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
            'scope': 'Whole h4/h5 absorption margins and the h(5/2) margin use the same actual S in [D,s]. Every fixed target selects its endpoint by coefficient sign. Vertex lower bounds do not assert concavity of epsilon. Independent original labels and complete tails retained; ordinary proof plus exact arithmetic, no Lean or unrestricted Erdos7 endpoint.'}
