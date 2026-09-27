"""Retain one actual raw source mass through the complete AP45 consumer.

The ordinary proof identifies the source deficits, raw positive hinges,
and survival denominator on the same actual mass S>=D. All internal s
terms in square357 stay in its raw bound. Original17/19 tests are separate.
"""
from fractions import Fraction as F
from hashlib import sha256
import json

CAPS = ((11, F(5, 3)), (13, F(12, 7)))
PAIRS = ((0, 0), (0, 1), (0, 2), (1, 0), (2, 0))
Q0 = F(919, 924)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def consumer(source, core, kc, previous_math, parent, previous, pure, rows,
             source_barrier, linear_increase):
    encode = previous_math.encode
    require(parent['caps'] == encode(CAPS) and parent['physical_thresholds'] == [4, 5],
            'Same actual AP11/T4 and AP13/T5 law')
    G, H16, H41 = (F(previous[key]) for key in ('source_G357', 'H16', 'H41'))
    require(G == F(102715, 2916), 'Same retained-event source-square theorem')
    outside = F(parent['quadratic_cost']['outside_active_first_moment'])
    norms = previous['norms']
    require([tuple(row['tuple']) for row in norms] == list(PAIRS), 'Five independent original quadratic costs')
    require(H16 == F(parent['quadratic_cost']['expectation'])
            + sum(F(row['C']) for row in norms)+outside*(G-1),
            'Complete fixed quadratic numerator before retaining raw deficits')
    linear = {row['name']: F(row['H']) for row in parent['linear_costs']}
    require(H41 == linear['R17']+source.P17*linear['R19']+source.EXTRA5*linear['R5'],
            'Complete old linear numerator and independent17/19 weights')
    old_H16, old_H41 = H16, H41
    old_H = source.AC*H16+H41
    require(isinstance(source_barrier, F) and isinstance(linear_increase, F)
            and source_barrier >= G and linear_increase >= 0,
            'Global rational comparison barriers dominate published constants')
    H16 += outside*(source_barrier-G)
    H41 += linear_increase
    H = source.AC*H16+H41
    finite, tails = source.ap_product_distribution(CAPS, 9)
    require(sum(finite.values())+tails[0] == 1
            and sum(n*n*p for n, p in finite.items())+tails[2] == F(1403, 630),
            'Complete AP45 product-count mass and second moment')
    finite_cap = sum(n*n*finite[n] for n in (7, 8))
    cG = tails[2]+finite_cap
    old_A81 = G*tails[2]-81*tails[0]+(G-1)*finite_cap
    A81 = old_A81+cG*(source_barrier-G)
    require(cG > 0 and A81 > 0, 'Positive retained square-norm coefficient')
    parameters = list(source.vertices())
    require(len(parameters) == len(rows) == 1296, 'Complete common parameter domain')
    old_rows, current_rows = [], []
    for index, (parameter, retained) in enumerate(zip(parameters, rows)):
        dat = source.data(parameter)
        s, D = dat[3:]
        require(retained['index'] == index and F(retained['s']) == s and F(retained['D']) == D,
                'Same actual source parameter and mass bounds')
        mg, Mquad, M41 = (F(retained[key]) for key in ('source_margin', 'Mquad', 'M41'))
        ms = tuple(F(value) for value in retained['quadratic_margins'])
        require(len(ms) == 5 and min((mg, Mquad, M41)+ms) >= 0
                and Mquad == sum(ms)+outside*mg, 'Complete nonnegative quadratic and linear deficits')
        B = source.raw357(F(4), dat)/6+F(4, 33)*source.raw357(F(5), dat)
        B += source.raw357(F(5, 2), dat)/22
        delta = Q0*D-B
        require(D > 0 and delta > 0 and delta == F(retained['Delta']),
                'Same actual AP survival raw numerator')
        # square357 is a raw upper bound. Its internal s terms are retained;
        # only the explicit complete-G slots use A81*S-cG*mg in the proof.
        raw81 = sum(p*n*n*source.square357(F(81, n*n), dat)
                    for n, p in finite.items() if n < 7)
        changed_D = dat[:4]+(D+1,)
        require(all(source.square357(F(81, n*n), changed_D)
                    == source.square357(F(81, n*n), dat) for n in finite if n < 7),
                'Finite raw square-hinge terms contain no hidden D normalization')
        old_rows.append({'index': index, 'D': D, 'Delta': delta, 'rho': delta/D,
                         'Gamma13': 16+D*old_H16/delta, 'T13_81': (old_A81*D+raw81)/delta,
                         'bound': source.WHOLE_CONST+D*old_H/delta})
        gamma = 16+(H16*D-Mquad)/delta
        t81 = (A81*D+raw81-cG*mg)/delta
        joint = source.WHOLE_CONST+(H*D-source.AC*Mquad-M41)/delta
        require(min(gamma-16, t81, joint-source.WHOLE_CONST) > 0,
                'Nonnegative upper numerators before the final survival division')
        current_rows.append({'index': index, 's': s, 'D': D, 'Delta': delta, 'B': B,
                             'source_margin': mg, 'Mquad': Mquad, 'M41': M41, 'Raw81': raw81,
                             'rho': delta/D, 'Gamma13': gamma, 'T13_81': t81,
                             'bound': joint, 'combined': joint+t81})

    old_targets = {key: max(row[key] for row in old_rows) for key in ('bound', 'Gamma13', 'T13_81')}
    old_digest = sha256(json.dumps(encode(old_rows), sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    require(all(value == F(previous[key]) for key, value in old_targets.items())
            and old_digest == previous['row_sha256'], 'Published independent consumer reconstructed exactly')
    old_rho = min(row['rho'] for row in old_rows)
    old_branches, old_rho = core.fallbacks(source, CAPS, G, old_targets, old_rho)
    old_source, old_errors = core.core_errors(kc, pure['source_inputs'], old_targets['Gamma13'],
                                            old_rho, old_targets['T13_81'], old_targets['bound'])
    require(encode(old_branches) == previous['fallbacks']
            and encode(old_source) == previous['source_inputs']
            and encode(old_errors) == previous['core_errors'], 'Every predecessor fallback and full core interface')

    targets = {key: max(row[key] for row in current_rows)
               for key in ('bound', 'Gamma13', 'T13_81', 'combined')}
    coefficients = {'bound': Q0*(targets['bound']-source.WHOLE_CONST)-H,
                    'Gamma13': Q0*(targets['Gamma13']-16)-H16,
                    'T13_81': Q0*targets['T13_81']-A81,
                    'combined': Q0*(targets['combined']-source.WHOLE_CONST)-H-A81}
    require(min(coefficients.values()) > 0, 'All four actual-S and separate-concavity coefficients')
    margins = {key: None for key in coefficients}
    margin_digest = sha256()
    for row in current_rows:
        D, delta, B = (row[key] for key in ('D', 'Delta', 'B'))
        mg, Mquad, M41, raw81 = (row[key] for key in ('source_margin', 'Mquad', 'M41', 'Raw81'))
        numerators = {'bound': H*D-source.AC*Mquad-M41,
                      'Gamma13': H16*D-Mquad,
                      'T13_81': A81*D+raw81-cG*mg,
                      'combined': (H+A81)*D+raw81-source.AC*Mquad-M41-cG*mg}
        constants = {'bound': source.WHOLE_CONST, 'Gamma13': F(16),
                     'T13_81': F(0), 'combined': source.WHOLE_CONST}
        corrections = {'bound': source.AC*Mquad+M41, 'Gamma13': Mquad,
                       'T13_81': cG*mg-raw81,
                       'combined': source.AC*Mquad+M41+cG*mg-raw81}
        for key in coefficients:
            target = targets[key]-constants[key]
            margin = target*delta-numerators[key]
            require(margin == coefficients[key]*D-target*B+corrections[key]
                    and margin >= 0, 'Expanded separately concave target margin: '+key)
            margins[key] = margin if margins[key] is None else min(margins[key], margin)
            margin_digest.update(f"{row['index']},{key}:{margin}\n".encode())
    rho = min(row['rho'] for row in current_rows)
    branch_targets = {key: targets[key] for key in ('bound', 'Gamma13', 'T13_81')}
    branches, rho = core.fallbacks(source, CAPS, G, branch_targets, rho)
    for branch in branches:
        branch['combined_bound'] = branch['bound']+branch['T13_81']
        branch['combined_margin'] = targets['combined']-branch['combined_bound']
        require(branch['combined_margin'] > 0, 'Every fallback combined bound below the main target')
    combined_gain = targets['bound']+targets['T13_81']-targets['combined']
    require(combined_gain >= 0, 'Same-parameter sum cannot exceed the separate maxima')
    source_inputs, errors = core.core_errors(kc, pure['source_inputs'], targets['Gamma13'],
                                           rho, targets['T13_81'], targets['bound'])
    for error in errors:
        error['combined_gap'] = targets['combined']+error['total']-403
        error['combined_safe_allowance'] = error['safe_allowance']+targets['T13_81']
        require(error['combined_gap'] == error['gap']-combined_gain
                and error['combined_safe_allowance'] < 403-error['total'],
                'Combined gap and strict complete-tail safety agree with separate notation')
    require(all(targets[key] < old_targets[key] for key in old_targets)
            and rho == old_rho == F(previous['rho']) and Q0-rho > 0,
            'Strict retained-deficit improvements and unchanged actual survival')
    require(len(branches) == 8 and len(errors) == 2, 'Every other source class and complete core')
    return {'source_G357': G, 'source_comparison_barrier': source_barrier,
            'predecessor_H16': old_H16, 'predecessor_H41': old_H41,
            'H41_increase': linear_increase, 'H16': H16, 'H41': H41, 'cG': cG, 'A81': A81,
            **targets, 'rho': rho, 'coefficients': coefficients,
            'survival_D_coefficient': Q0-rho, 'minimum_margins': margins,
            'combined_target_gain': combined_gain,
            'source_inputs': source_inputs, 'fallbacks': branches, 'core_errors': errors,
            'maximizers': {key: [row['index'] for row in current_rows if row[key] == value]
                           for key, value in targets.items()},
            'consumer_vertex_checks': 1296, 'consumer_target_margin_checks': 5184,
            'predecessor_consumer_vertex_checks': 1296, 'fallback_checks': 8, 'complete_core_checks': 2,
            'consumer_margin_sha256': margin_digest.hexdigest(),
            'row_sha256': sha256(json.dumps(encode(current_rows), sort_keys=True,
                                           separators=(',', ':')).encode()).hexdigest(),
            'scope': 'One actual raw357 mass S through AP45 and one final conditioning, independent original17/19 tests, complete tails. All four final fixed-target margins are separately concave after S>=D. Ordinary proof and exact arithmetic; no Lean, negative-Q or unrestricted Erdos7 endpoint.'}
