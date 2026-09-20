"""Five AP45 quadratic norms retaining the original 5,15,45 events.

Fixed rational inputs are checked over the whole parameter domain. No root
search or height truncation is performed. The ordinary proof supplies the
actual-event payment and separate-concavity arguments; this is not Lean.
"""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import json

PAIRS = ((0, 0), (0, 1), (0, 2), (1, 0), (2, 0))
CAPS = ((11, F(5, 3)), (13, F(12, 7)))
QD = F(919, 924)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def rational(value):
    require(type(value) is str, 'Rational input is a string')
    result = F(value)
    require(str(result) == value, 'Canonical rational input')
    return result


def _distance(eta, b, c):
    delta = tuple(x-y for x, y in zip(b, c))
    return sum(w*v*v for w, v in zip(eta, delta)) - (
        max((0,)+delta)**2+max((0,)+tuple(-v for v in delta))**2)/F(18)


def norms(source, fixed, layout, ap, parent, inputs, progress=None):
    require(type(inputs) is dict and set(inputs) == {'schema', 'constants'}
            and inputs['schema'] == 'erdos7-retained-quadratic-input-v1', 'Exact norm input schema')
    given = inputs['constants']
    require(type(given) is list and len(given) == 5, 'Five quadratic inputs')
    old = [row for row in parent['norms'] if row['name'] == 'H16']
    require([tuple(row['tuple']) for row in old] == list(PAIRS), 'Five original parent tuples')
    roots = (0, 0, 1, 1, 1)
    bases = tuple(tuple(1+int(roots[i] == r)+int(i == j) for i in range(5))
                  for r in range(2) for j in range(5))
    require(source.ROOT == roots and source.BASES == bases, 'Exact independent original layouts')
    items = []
    for pair, row, previous in zip(PAIRS, given, old):
        require(type(row) is dict and set(row) == {'tuple', 'constant'}
                and type(row['tuple']) is list and len(row['tuple']) == 2
                and all(type(v) is int for v in row['tuple'])
                and tuple(row['tuple']) == pair, 'Original tuple identity and order')
        C = rational(row['constant'])
        require(0 < C < F(previous['joint']), 'Strict improvement of the same norm')
        tag = ('ap_block', (('s', F(16)), CAPS, *pair))
        zero, psi, curve, _, record = ap.psi_record(source, layout, pair)
        f = lambda v: source.zero5_cost(tag, v)
        increment = f(4)-f(3)
        floor = f(3)+3*increment
        deep = (C-f(3))/4-3*increment/5
        require(C > floor and deep > 0, 'Strict full-domain unclipped and deep conditions')
        payment = tuple(psi(v+1)-psi(v)-F(6, 5)*(f(v+1)-f(v)) for v in range(1, 5))
        require(min(payment) >= 0 and source.zero5_cost_metadata(zero)[1]
                == F(6, 5)*source.zero5_cost_metadata(tag)[1], 'Pre-tail payment and exact tail leading term')
        items.append({'tuple': pair, 'C': C, 'previous_C': F(previous['joint']),
                      'tag': tag, 'zero': zero, 'psi': psi, 'curve': curve,
                      'curvature_record': record, 'payment_increment_margins': payment,
                      'maximum_floor': floor, 'minimum_deep_formula': deep,
                      'minimum_margin': None, 'minimum_signed_sum': None, 'minimum_deep': None,
                      'zero_margins': [], 'checks': 0, 'digest': sha256()})

    @lru_cache(None)
    def positive(ci, eta):
        item = items[ci]
        zero, psi = item['zero'], item['psi']
        degree, a, z, cutoff = source.zero5_cost_metadata(zero)
        require(degree == 2 and cutoff >= 2, 'Exact polynomial-tail metadata')
        x = sum(eta)
        tails = tuple(4*t for t in source.geom(5, cutoff))
        squares = tuple(source.sq_value(F(0), b, eta, source.ONES) for b in bases)
        raw = {n: tuple(source.zero5_scaled_pure(zero, n, b, eta) for b in bases)
               for n in range(2, cutoff)}
        constant = sum(F(4, 5**n)*psi(n) for n in range(2, cutoff)) + a*tails[2]+z*tails[0]
        result = []
        for li in range(10):
            value = sum(F(4, 5**n)*(raw[n][li]-psi(n)*x
                        +(n-2)*(max(raw[n])-psi(n)*x))/n for n in range(2, cutoff))
            value += a*tails[1]*(squares[li]-x)
            value += a*(tails[2]-2*tails[1])*(max(squares)-x)+constant*x
            result.append(value)
        previous = source.zero5_positive_with_constant(zero, eta)
        rebuilt = sum(F(4*(n-1), 5**n)*(max(raw[n])-psi(n)*x)/n for n in range(2, cutoff))
        rebuilt += a*(tails[2]-tails[1])*(max(squares)-x)+constant*x
        require(rebuilt == previous and max(result) <= previous,
                'Whole-tail positive source reconstruction and retained-layout domination')
        return tuple(result)

    parameters = list(source.vertices())
    require(len(parameters) == 1296, 'Complete five-group parameter domain')
    for index, par in enumerate(parameters):
        dat = source.data(par)
        d, mass, eta, s, D = dat
        require(min(d) >= F(1, 4) and min(mass) >= 0 and D > 0, 'Original source domain')
        for ci, item in enumerate(items):
            C, tag, zero, psi, curve = (item[k] for k in ('C', 'tag', 'zero', 'psi', 'curve'))
            common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
            raw2 = tuple(source.zero5_scaled_pure(zero, 2, c, eta) for c in bases)
            for bi, b in enumerate(bases):
                fb = tuple(source.zero5_cost(tag, v) for v in b)
                inc = tuple(source.zero5_cost(tag, v+1)-source.zero5_cost(tag, v) for v in b)
                k = tuple(C-v for v in fb)
                base = sum(mass[j]*psi(b[j])+eta[j]*source.zero5_centered_correction(zero, b[j])
                           for j in range(5))
                base += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
                distances = tuple(_distance(eta, b, c) for c in bases)
                require(min(distances) >= 0, 'Actual pure3 layout-distance lower bounds')
                oldgap = F(2, 25)*(max(raw2)-max(v-2*curve*t for v, t in zip(raw2, distances)))
                oldselected = common+base+source.zero5_positive_with_constant(zero, eta)-oldgap
                for li, c in enumerate(bases):
                    correction = tuple(v*t for v, t in zip(inc, c))
                    require(C >= max(v+u for v, u in zip(fb, correction)), 'Actual selected-event floor')
                    selected = common+base+positive(ci, eta)[li]-F(4, 25)*curve*distances[li]
                    require(selected <= oldselected, 'Coupled selected source improves the old comparison')
                    signed = sum(k[j]*mass[j]-correction[j]*eta[j]/5 for j in range(5))
                    deep = min(k[j]*d[j]-correction[j]/5 for j in range(5))
                    require(signed > 0 and deep > 0, 'Strict empty-carrier and deep signs')
                    margin = C*s-selected-fixed._cofactor_cap(dat, k, correction, 6)/5
                    require(margin >= 0, 'Retained quadratic margin: '+str((ci, index, bi, li)))
                    for key, value in (('minimum_margin', margin), ('minimum_signed_sum', signed),
                                       ('minimum_deep', deep)):
                        item[key] = value if item[key] is None else min(item[key], value)
                    if margin == 0:
                        item['zero_margins'].append([index, bi, li])
                    item['digest'].update(f'{index},{bi},{li}:{margin}\n'.encode())
                    item['checks'] += 1
        if progress is not None:
            progress(index+1, len(parameters))
    result = []
    for item in items:
        require(item['checks'] == 129600 and item['minimum_margin'] == 0
                and item['minimum_deep'] == item['minimum_deep_formula'], 'Complete norm domain and strict deep identity')
        row = {key: item[key] for key in ('tuple', 'C', 'previous_C', 'curvature_record',
               'payment_increment_margins', 'maximum_floor', 'minimum_deep_formula',
               'minimum_margin', 'minimum_signed_sum', 'minimum_deep', 'zero_margins', 'checks')}
        row['floor_slack'] = item['C']-item['maximum_floor']
        row['margin_sha256'] = item['digest'].hexdigest()
        result.append(row)
    return result


def consumer(source, core, kc, previous_math, parent, previous, pure, norm_results):
    G = F(previous['source_G357'])
    require(G == F(102715, 2916), 'Same previously proved uniform357 source')
    old = previous_math.consumer(source, core, kc, parent, pure, G)
    require(all(encode(value) == previous[key] for key, value in old.items()),
            'Whole published source-improved AP45 consumer reproduced')
    gain = sum(row['previous_C']-row['C'] for row in norm_results)
    H16, H41 = old['H16']-gain, old['H41']
    _, tail4 = previous_math._product_distribution(4)
    outside = F(parent['quadratic_cost']['outside_active_first_moment'])
    require(H16 == tail4[2]-16*tail4[0]+sum(row['C'] for row in norm_results)+outside*(G-1),
            'Complete quadratic expectation, five norms and infinite tuple complement')
    finite, tail = previous_math._product_distribution(9)
    coefficient81 = G*tail[2]-81*tail[0]+(G-1)*sum(n*n*finite[n] for n in (7, 8))
    rows = []
    for index, par in enumerate(source.vertices()):
        dat = source.data(par)
        D = dat[4]
        delta = QD*D-source.raw357(F(4), dat)/6
        delta -= F(4, 33)*source.raw357(F(5), dat)+source.raw357(F(5, 2), dat)/22
        require(D > 0 and delta > 0, 'Unchanged actual AP45 survival')
        u81 = coefficient81*D+sum(prob*n*n*source.square357(F(81, n*n), dat)
                                  for n, prob in finite.items() if n < 7)
        rows.append({'index': index, 'D': D, 'Delta': delta, 'rho': delta/D,
                     'Gamma13': 16+D*H16/delta, 'T13_81': u81/delta,
                     'bound': source.WHOLE_CONST+D*(source.AC*H16+H41)/delta})
    require(len(rows) == 1296, 'Complete consumer parameter domain')
    targets = {key: max(row[key] for row in rows) for key in ('bound', 'Gamma13', 'T13_81')}
    rho = min(row['rho'] for row in rows)
    coefficients = {'bound': (targets['bound']-source.WHOLE_CONST)*QD-source.AC*H16-H41,
                    'Gamma13': (targets['Gamma13']-16)*QD-H16,
                    'T13_81': targets['T13_81']*QD-coefficient81, 'survival': QD-rho}
    require(min(coefficients.values()) > 0, 'Every continuous-extension coefficient')
    branches, rho = core.fallbacks(source, CAPS, G, targets, rho)
    source_inputs, errors = core.core_errors(kc, pure['source_inputs'], targets['Gamma13'],
                                           rho, targets['T13_81'], targets['bound'])
    require(len(branches) == 8 and len(errors) == 2, 'Every fallback and complete finite-core interface')
    require(targets['bound'] < old['bound'] and targets['Gamma13'] < old['Gamma13']
            and targets['T13_81'] == old['T13_81'] and rho == old['rho'],
            'Strict same-law consumer improvement with unchanged hinge and survival')
    return {'source_G357': G, 'H16': H16, 'H41': H41, 'quadratic_H16_gain': gain,
            **targets, 'rho': rho, 'coefficients': coefficients, 'source_inputs': source_inputs,
            'fallbacks': branches, 'core_errors': errors,
            'maximizers': {key: [row['index'] for row in rows if row[key] == value]
                           for key, value in targets.items()},
            'row_sha256': sha256(json.dumps(encode(rows), sort_keys=True,
                                           separators=(',', ':')).encode()).hexdigest()}


def reconstruct(source, fixed, layout, ap, core, kc, previous_math, parent, previous, pure, inputs, progress=None):
    norm_results = norms(source, fixed, layout, ap, parent, inputs, progress)
    current = consumer(source, core, kc, previous_math, parent, previous, pure, norm_results)
    return encode({'schema': 'erdos7-retained-quadratic-tests-v1', **current,
                   'norms': norm_results, 'norm_margin_checks': 648000,
                   'consumer_vertex_checks': 1296, 'predecessor_consumer_vertex_checks': 1296,
                   'fallback_checks': 8, 'complete_core_checks': 2,
                   'verification_scope': '648000 final quadratic norm margins, complete AP45 consumer and predecessor consumer, eight missing-class branches and both full finite-core tails. The existing source and linear norm proofs are reused, not replayed.',
                   'scope': 'Same actual AP(4,5), independent original residues, complete tails and one final conditioning. Ordinary proof and exact rational arithmetic; no actual-family sharpness, Lean endpoint, negative Q or unrestricted Erdos7 resolution.'})
