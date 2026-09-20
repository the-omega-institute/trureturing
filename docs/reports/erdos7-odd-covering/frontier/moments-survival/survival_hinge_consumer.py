"""Propagate a signed survival-hinge deficit through one actual source mass."""
from fractions import Fraction as F
from hashlib import sha256
import json

Q = F(193, 231)
CAPS = ((11, F(5, 3)), (13, F(12, 7)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def consume(source, core, kc, encode, previous, pure, rows):
    H16, H41, cG, A81 = (F(previous[k]) for k in ('H16', 'H41', 'cG', 'A81'))
    H = source.AC*H16+H41
    require(F(previous['source_comparison_barrier']) == 45
            and F(previous['source_G357']) == F(102715, 2916), 'Distinct unchanged square norm and barrier')
    parameters = list(source.vertices())
    require(len(rows) == len(parameters) == 1296, 'Complete actual source parameter domain')
    finite, tails = source.ap_product_distribution(CAPS, 9)
    require(cG == tails[2]+sum(n*n*finite[n] for n in (7, 8)), 'Unchanged complete square tail coefficient')
    current = []
    for index, (parameter, row) in enumerate(zip(parameters, rows)):
        dat = source.data(parameter)
        s, D = dat[3:]
        require(row['index'] == index and (row['s'], row['D']) == (s, D),
                'Original common forbidden-family source parameter')
        mg, Mq, Ml, m = (row[k] for k in ('source_margin', 'Mquad', 'M41', 'survival_hinge_margin'))
        B = source.raw357(F(4), dat)/6+F(4, 33)*source.raw357(F(5), dat)-m/22
        delta = Q*D-B
        require(D > 0 and delta > 0, 'Positive signed raw survival denominator at the D endpoint')
        raw81 = sum(prob*n*n*source.square357(F(81, n*n), dat)
                    for n, prob in finite.items() if n < 7)
        gamma = 16+(H16*D-Mq)/delta
        joint = source.WHOLE_CONST+(H*D-source.AC*Mq-Ml)/delta
        t81 = (A81*D+raw81-cG*mg)/delta
        require(min(gamma-16, joint-source.WHOLE_CONST, t81) > 0,
                'Positive target candidates before the actual-S sign checks')
        current.append({'index': index, 's': s, 'D': D, 'B': B, 'Delta': delta,
                        'source_margin': mg, 'Mquad': Mq, 'M41': Ml,
                        'survival_hinge_margin': m, 'Raw81': raw81,
                        'bound': joint, 'Gamma13': gamma, 'T13_81': t81,
                        'combined': joint+t81, 'rho': delta/D})
    keys = ('bound', 'Gamma13', 'T13_81', 'combined')
    targets = {k: max(r[k] for r in current) for k in keys}
    rho = min(r['rho'] for r in current)
    coeff = {'bound': Q*(targets['bound']-source.WHOLE_CONST)-H,
             'Gamma13': Q*(targets['Gamma13']-16)-H16,
             'T13_81': Q*targets['T13_81']-A81,
             'combined': Q*(targets['combined']-source.WHOLE_CONST)-H-A81,
             'rho': Q-rho}
    require(rho > 0 and min(coeff.values()) > 0, 'All five common actual-mass coefficients are positive')
    digest, minima = sha256(), {k: None for k in coeff}
    count = 0
    for row in current:
        D, B, delta, raw81, mg, Mq, Ml = (row[k] for k in
                                         ('D', 'B', 'Delta', 'Raw81', 'source_margin', 'Mquad', 'M41'))
        numerators = {'bound': H*D-source.AC*Mq-Ml, 'Gamma13': H16*D-Mq,
                      'T13_81': A81*D+raw81-cG*mg,
                      'combined': (H+A81)*D+raw81-source.AC*Mq-Ml-cG*mg}
        constants = {'bound': source.WHOLE_CONST, 'Gamma13': F(16),
                     'T13_81': F(0), 'combined': source.WHOLE_CONST}
        correction = {'bound': source.AC*Mq+Ml, 'Gamma13': Mq,
                      'T13_81': cG*mg-raw81, 'combined': source.AC*Mq+Ml+cG*mg-raw81}
        margins = {'rho': delta-rho*D}
        require(margins['rho'] == coeff['rho']*D-B, 'Expanded signed survival target')
        for k in keys:
            t = targets[k]-constants[k]
            margins[k] = t*delta-numerators[k]
            require(margins[k] == coeff[k]*D-t*B+correction[k], 'Expanded actual-S cost target: '+k)
        for k, margin in margins.items():
            require(isinstance(margin, F) and margin >= 0, 'Exact nonnegative final target margin: '+k)
            minima[k] = margin if minima[k] is None else min(minima[k], margin)
            digest.update(f"{row['index']},{k}:{margin}\n".encode())
            count += 1
    branch_targets = {k: targets[k] for k in keys if k != 'combined'}
    branches, total_rho = core.fallbacks(source, CAPS, F(previous['source_G357']), branch_targets, rho)
    require(total_rho == rho, 'All eight complete branches preserve the reported survival lower bound')
    for branch in branches:
        branch['combined_bound'] = branch['bound']+branch['T13_81']
        require(branch['combined_bound'] < targets['combined'], 'Every complete fallback joint target')
    source_inputs, errors = core.core_errors(kc, pure['source_inputs'], targets['Gamma13'], rho,
                                           targets['T13_81'], targets['bound'])
    combined_gain = targets['bound']+targets['T13_81']-targets['combined']
    require(combined_gain >= 0, 'Common-parameter target dominates the separate maxima')
    for error in errors:
        error['combined_gap'] = targets['combined']+error['total']-403
        require(error['combined_gap'] == error['gap']-combined_gain, 'Same complete-core gap')
    require(count == 6480 and len(branches) == 8 and len(errors) == 2,
            'Five complete target sets, eight source branches and both complete cores')
    require(all(targets[k] < F(previous[k]) for k in keys) and rho > F(previous['rho']),
            'All targets and actual survival strictly improve the published predecessor')
    return {**targets, 'rho': rho, 'q_effective': Q, 'H16': H16, 'H41': H41, 'cG': cG, 'A81': A81,
            'source_G357': F(previous['source_G357']), 'source_comparison_barrier': F(45),
            'coefficients': coeff, 'minimum_margins': minima, 'combined_target_gain': combined_gain,
            'maximizers': {k: [r['index'] for r in current if r[k] == targets[k]] for k in keys},
            'rho_minimizers': [r['index'] for r in current if r['rho'] == rho],
            'source_inputs': source_inputs, 'fallbacks': branches, 'core_errors': errors,
            'consumer_vertex_checks': 1296, 'consumer_target_margin_checks': count,
            'fallback_checks': 8, 'complete_core_checks': 2,
            'consumer_margin_sha256': digest.hexdigest(),
            'row_sha256': sha256(json.dumps(encode(current), sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
            'scope': 'The h(5/2) deficit and all numerator deficits use one actual raw survivor mass. Signed B is allowed; positivity follows from the separate survival target. Independent original labels and all exponent tails remain complete. Ordinary inequalities and exact rational verification, no Lean or unrestricted Erdos7 endpoint.'}
