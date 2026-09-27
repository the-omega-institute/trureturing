"""Exact source and AP(4,5) bounds retaining the original 5,15,45 tests.

The accompanying ordinary proof supplies the actual-event inequalities and
continuous-domain extension. This module checks their complete rational
parameter domain and reuses the published full-tail consumer primitives.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod
import json

G = F(102715, 2916)
CAPS = ((11, F(5, 3)), (13, F(12, 7)))
PAIRS = ((0, 0), (0, 1), (0, 2), (1, 0), (2, 0))
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


def _root(values):
    return max(sum(values[:2]), sum(values[2:]))


def _distance(eta, b, c):
    delta = tuple(x-y for x, y in zip(b, c))
    return sum(w*x*x for w, x in zip(eta, delta)) - (
        max((0,) + delta)**2
        + max((0,) + tuple(-x for x in delta))**2) / F(18)


def _cap(dat, constant, b, c):
    d, mass, eta, _, _ = dat
    k = tuple(constant-x*x for x in b)
    correction = tuple((2*x+1)*y for x, y in zip(b, c))
    require(constant >= 30 and all(0 <= v <= u for v, u in zip(correction, k)),
            'Unclipped original 5,15,45 event floor')
    signed = tuple(k[j]*mass[j]-correction[j]*eta[j]/5 for j in range(5))
    deep = tuple(k[j]*d[j]-F(correction[j], 5) for j in range(5))
    require(sum(signed) >= 0 and min(deep) >= 0,
            'Empty cofactor alternatives and nonnegative deep coefficients')
    weighted = tuple(9*eta[j]*k[j] for j in range(5))
    return (_root(signed) + max(signed) + F(40, 729)*max(deep)
            + F(1, 1458)*max(k[j]*d[j] for j in range(5))
            + (sum(weighted)+_root(weighted)+max(weighted))/36 + max(k)/72)


def source_norm(source, parent, previous):
    old = F(parent['source_G357'])
    require(old == F(previous['source_G357']) == F(1730443, 48600) > G,
            'Published source predecessor and strict proposed improvement')
    roots = (0, 0, 1, 1, 1)
    layouts = tuple(tuple(1+int(roots[i] == r)+int(i == j) for i in range(5))
                    for r in range(2) for j in range(5))
    require(source.ROOT == roots and source.BASES == layouts,
            'Exact ten original shallow layouts')
    parameters = list(source.vertices())
    require(len(parameters) == 1296, 'Complete five-group parameter domain')
    zero = ('seven_block', (('s', F(0)), 0))
    digest, old_digest = sha256(), sha256()
    checks = old_checks = 0
    minimum, old_minimum = None, None
    zeros, old_zeros = [], []
    for index, par in enumerate(parameters):
        dat = source.data(par)
        d, mass, eta, s, D = dat
        require(min(d) >= F(1, 4) and min(mass) >= 0 and D > 0,
                'Actual parameter density, mass and survival bounds')
        pure = tuple(sum(w*x*x for w, x in zip(eta, b))
                     + max(F(x+1, 9) for x in b) for b in layouts)
        M = max(pure)
        base = tuple(sum((n+e/4)*x*x for n, e, x in zip(mass, eta, b))
                     + max((v+F(1, 4))*F(x+1, 9) for v, x in zip(d, b))
                     for b in layouts)
        global35 = max(base)+F(5, 8)*M
        require(global35 == source.zero5_raw(('s', F(0)), dat),
                'Complete unchanged global raw35 square')
        raw = tuple(source.zero5_scaled_pure(zero, 2, c, eta) for c in layouts)
        remainder = (source.zero7_raw(('s', F(0)), dat)-source.zero5_raw(zero, dat)
                     + source.zero5_positive_with_constant(zero, eta))
        for bi, b in enumerate(layouts):
            distances = tuple(_distance(eta, b, c) for c in layouts)
            require(min(distances) >= 0, 'Nonnegative original-layout distance')
            oldmax = max(base[bi]+F(61, 200)*M+F(8, 25)*Mc-F(4, 25)*dist
                         for Mc, dist in zip(pure, distances))
            saving = F(2, 25)*(max(raw)-max(
                v-F(12, 5)*dist for v, dist in zip(raw, distances)))
            canonical = remainder + sum(
                mass[j]*F(6, 5)*(b[j]*b[j]-1)
                + eta[j]*source.zero5_centered_correction(zero, b[j]) for j in range(5))
            canonical += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
            canonical -= saving
            require(F(6, 5)*oldmax+F(7, 15)*global35 == canonical,
                    'Exact reconstruction of the complete published selected source')
            old_margin = old*s-canonical-_cap(dat, old, b, (1,)*5)/5
            require(old_margin >= 0, 'Published source margin remains valid')
            old_minimum = old_margin if old_minimum is None else min(old_minimum, old_margin)
            if old_margin == 0:
                old_zeros.append([index, bi])
            old_digest.update(f'{index},{bi}:{canonical}:{old_margin}\n'.encode())
            old_checks += 1
            for ci, (c, Mc, dist) in enumerate(zip(layouts, pure, distances)):
                selected = base[bi]+F(9, 20)*Mc+F(7, 40)*M-F(4, 25)*dist
                numerator = F(6, 5)*selected+F(7, 15)*global35+_cap(dat, G, b, c)/5
                margin = G*s-numerator
                require(margin >= 0, 'Retained-five source margin: '+str((index, bi, ci)))
                minimum = margin if minimum is None else min(minimum, margin)
                if margin == 0:
                    zeros.append([index, bi, ci])
                digest.update(f'{index},{bi},{ci}:{margin}\n'.encode())
                checks += 1
    fallbacks = (F(5273, 258), F(14543, 438))
    require(max(fallbacks) < G and minimum == old_minimum == 0,
            'Strict missing-class bounds and active source witnesses')
    require(old_zeros == previous['norms'][0]['zero_margins'],
            'Exact published source control rows')
    require((checks, old_checks) == (129600, 12960), 'Complete source check counts')
    return {'previous_G357': old, 'improvement': old-G, 'source_margin_checks': checks,
            'canonical_source_formula_checks': old_checks, 'minimum_margin': minimum,
            'zero_margins': zeros, 'margin_sha256': digest.hexdigest(),
            'canonical_source_sha256': old_digest.hexdigest(),
            'published_zero_margins': old_zeros, 'missing_class_bounds': fallbacks}


def _probability(prime, cap, n):
    return 1-cap/prime if n == 1 else cap*(prime-1)/prime**n


def _product_distribution(cutoff):
    finite = {}
    for i, j in product(range(1, cutoff), repeat=2):
        if i*j < cutoff:
            probability = _probability(11, F(5, 3), i)*_probability(13, F(12, 7), j)
            finite[i*j] = finite.get(i*j, F(0))+probability
    moments = (F(1), prod(1+c/(p-1) for p, c in CAPS),
               prod(1+c*F(3*p-1, (p-1)**2) for p, c in CAPS))
    require(moments[1:] == (F(4, 3), F(1403, 630)), 'Complete AP45 geometric moments')
    tails = tuple(moments[k]-sum(n**k*w for n, w in finite.items()) for k in range(3))
    require(min(tails) >= 0, 'Complete nonnegative product-count tails')
    return finite, tails


def _active_first(prime, cap, exponent):
    if exponent == 0:
        return 1+cap/(prime-1)
    return cap/prime**exponent*(exponent+1+F(1, prime-1))


def consumer(source, core, kc, parent, pure, constant):
    require(encode(CAPS) == parent['caps'] and parent['physical_thresholds'] == [4, 5],
            'Same actual AP45 probability and physical thresholds')
    _, tail4 = _product_distribution(4)
    expectation = tail4[2]-16*tail4[0]
    outside = F(1403, 630)-sum(_active_first(11, F(5, 3), e)
                                *_active_first(13, F(12, 7), f) for e, f in PAIRS)
    require(expectation == F(parent['quadratic_cost']['expectation'])
            and outside == F(parent['quadratic_cost']['outside_active_first_moment']),
            'Complete parent quadratic expectation and original-tuple complement')
    quadratic = [row for row in parent['norms'] if row['name'] == 'H16']
    require([tuple(row['tuple']) for row in quadratic] == list(PAIRS),
            'Same five independently certified quadratic costs')
    H16 = expectation+sum(F(row['joint']) for row in quadratic)+outside*(constant-1)
    require(H16 == F(parent['H16'])+outside*(constant-F(parent['source_G357'])),
            'Independent old/new quadratic normalization')
    linear = {row['name']: F(row['H']) for row in parent['linear_costs']}
    H41 = linear['R17']+source.P17*linear['R19']+source.EXTRA5*linear['R5']
    require(H41 == F(parent['H41']), 'Unchanged complete linear cost bounds')
    finite, tail = _product_distribution(9)
    require((finite, tail) == source.ap_product_distribution(CAPS, 9),
            'Independent complete N11*N13 distribution')
    coefficient81 = constant*tail[2]-81*tail[0]
    coefficient81 += (constant-1)*sum(n*n*finite[n] for n in (7, 8))
    rows = []
    for index, par in enumerate(source.vertices()):
        dat = source.data(par)
        D = dat[4]
        delta = QD*D-source.raw357(F(4), dat)/6
        delta -= F(4, 33)*source.raw357(F(5), dat)+source.raw357(F(5, 2), dat)/22
        require(D > 0 and delta > 0, 'Same actual AP45 survival denominator')
        u81 = coefficient81*D+sum(prob*n*n*source.square357(F(81, n*n), dat)
                                  for n, prob in finite.items() if n < 7)
        rows.append({'index': index, 'D': D, 'Delta': delta, 'rho': delta/D,
                     'Gamma13': 16+D*H16/delta, 'T13_81': u81/delta,
                     'bound': source.WHOLE_CONST+D*(source.AC*H16+H41)/delta})
    require(len(rows) == 1296, 'Complete AP45 consumer domain')
    targets = {key: max(row[key] for row in rows) for key in ('bound', 'Gamma13', 'T13_81')}
    rho = min(row['rho'] for row in rows)
    coefficients = {'bound': (targets['bound']-source.WHOLE_CONST)*QD-source.AC*H16-H41,
                    'Gamma13': (targets['Gamma13']-16)*QD-H16,
                    'T13_81': targets['T13_81']*QD-coefficient81, 'survival': QD-rho}
    require(min(coefficients.values()) > 0, 'All continuous-domain extension coefficients')
    branches, rho = core.fallbacks(source, CAPS, constant, targets, rho)
    source_inputs, errors = core.core_errors(kc, pure['source_inputs'], targets['Gamma13'],
                                           rho, targets['T13_81'], targets['bound'])
    require(len(branches) == 8 and len(errors) == 2, 'All fallback and complete core interfaces')
    return {'source_G357': constant, 'H16': H16, 'H41': H41, **targets, 'rho': rho,
            'coefficients': coefficients, 'source_inputs': source_inputs, 'fallbacks': branches,
            'core_errors': errors,
            'maximizers': {key: [row['index'] for row in rows if row[key] == value]
                           for key, value in targets.items()},
            'row_sha256': sha256(json.dumps(encode(rows), sort_keys=True,
                                           separators=(',', ':')).encode()).hexdigest()}


def reconstruct(source, core, kc, parent, previous, pure):
    norm = source_norm(source, parent, previous)
    old = consumer(source, core, kc, parent, pure, F(parent['source_G357']))
    require(all(old[key] == F(parent[key]) for key in ('bound', 'Gamma13', 'T13_81'))
            and old['row_sha256'] == parent['consumer_row_sha256'],
            'Exact published AP45 consumer reconstruction')
    require(encode(old['fallbacks']) == parent['other_eight_branches']
            and encode(old['core_errors']) == parent['core_errors']
            and encode(old['source_inputs']) == parent['source_inputs'],
            'Every published fallback and finite-core interface reproduced')
    current = consumer(source, core, kc, parent, pure, G)
    require(all(current[key] < old[key] for key in ('bound', 'Gamma13', 'T13_81')),
            'Strict improvements of all three complete consumer targets')
    require(current['rho'] == old['rho'], 'Unchanged actual global survival lower bound')
    return encode({'schema': 'erdos7-retained-five-tests-v1', **current,
                   'source_norm': norm, 'consumer_vertex_checks': 1296,
                   'predecessor_consumer_vertex_checks': 1296, 'fallback_checks': 8,
                   'complete_core_checks': 2,
                   'verification_scope': '129600 new source margins, 12960 published selected-source reconstructions, complete AP45 consumer vertices, eight missing-class branches and both full finite-core tails. Parent AP norm theorems are reused, not replayed.',
                   'scope': 'Actual uniform357 source and actual AP(4,5) throughout, with independent original residues and complete tails. Ordinary proof and exact rational arithmetic; no actual-family sharpness, Lean endpoint, negative-Q conclusion or unrestricted Erdos7 resolution.'})
