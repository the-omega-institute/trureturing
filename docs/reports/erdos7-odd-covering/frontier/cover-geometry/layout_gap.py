"""Final exact checks for the original-layout N5=2 Jensen gap.

No search, fitted root, finite-height truncation or mutable source globals.
The supplied source API and two predecessor certificates remain unchanged.
"""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import prod
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def _rational(value):
    require(type(value) is str, 'Rational input is a string')
    result = F(value)
    require(str(result) == value, 'Canonical rational input')
    return result


def _probability(p, cap, n):
    return 1 - cap / p if n == 1 else cap * F(p - 1, p ** n)


def _active_first(p, cap, e):
    return 1 + cap / (p - 1) if e == 0 else cap / p ** e * (e + 1 + F(1, p - 1))


def _psi_record(source, pair):
    """The full zero7 cost, from its complete first moment and K<4 atoms.

    psi(v)=A(v²-1)+sum_{k<4} p_k/k [(16-k²v²)+-(16-k²)+].
    Thus its tail is exactly quadratic for every v>=4, not sampled.
    """
    if pair is None:
        tag, mean, atoms = ('s', F(0)), F(6, 5), {}
    else:
        e, f = pair
        tag = ('ap_block', (('s', F(16)), source.CAP13, e, f))
        mean = F(6, 5) * _active_first(11, F(5, 3), e) * _active_first(13, F(2), f)
        atoms = {}
        for k in range(1, 4):
            atoms[k] = sum(
                (F(29, 35) if n7 == 1 else F(36, 5 * 7 ** n7))
                * _probability(11, F(5, 3), n11) * _probability(13, F(2), n13)
                for n7 in range(1, k + 1) for n11 in range(1, k + 1)
                for n13 in range(1, k + 1)
                if n7 * n11 * n13 == k and n11 > e and n13 > f)
    zero = ('seven_block', (tag, 0))

    def psi(v):
        return mean * (v * v - 1) + sum(
            F(p) / k * (max(F(16 - k * k * v * v), F(0)) - (16 - k * k))
            for k, p in atoms.items())

    curvature = min((psi(k + 1) - 2 * psi(k) + psi(k - 1)) / 2 for k in range(2, 6))
    degree, leading, constant, cutoff = source.zero5_cost_metadata(zero)
    require(degree == 2 and leading == mean and cutoff <= 4,
            'Full quadratic tail from the same original cost')
    require(constant == psi(4) - mean * 16 and curvature > 0,
            'Exact polynomial tail and strictly positive integer curvature')
    require(all(source.zero5_cost(zero, v) == psi(v) for v in range(1, 6)),
            'Every pre-tail source value agrees with independent count formula')
    require((psi(6) - 2 * psi(5) + psi(4)) / 2 == mean,
            'First all-tail curvature equals the complete first moment')
    return tag, zero, psi, mean, curvature


def _cofactor_cap(source, dat, C, fb, increment):
    d, mass, eta, _, _ = dat
    k = tuple(C - v for v in fb)
    require(all(0 <= c <= v for c, v in zip(increment, k)), 'Unclipped four-load floor')
    signed = tuple(k[j] * mass[j] - increment[j] * eta[j] / 5 for j in range(5))
    deep = tuple(k[j] * d[j] - increment[j] / 5 for j in range(5))
    require(sum(signed) >= 0 and min(deep) >= 0, 'Empty labels and signed deep coefficients')
    root = lambda x: max(sum(x[:2]), sum(x[2:]))
    weighted = tuple(9 * eta[j] * k[j] for j in range(5))
    return (root(signed) + max(signed) + F(40, 729) * max(deep)
            + F(1, 1458) * max(k[j] * d[j] for j in range(5))
            + (sum(weighted) + root(weighted) + max(weighted)) / 36 + max(k) / 72)


def reconstruct(source, consumer, previous, inputs, progress=None):
    """Check six final fixed norms and their unchanged-AP(4,6) consumer."""
    require(set(inputs) == {'schema', 'source_square_bound', 'quadratic_constants'}, 'Exact input fields')
    require(inputs['schema'] == 'erdos7-layout-gap-norm-input-v1', 'Input schema')
    require(source.CAP13 == ((11, F(5, 3)), (13, F(2))), 'Unchanged actual AP(4,6) law')
    roots = (0, 0, 1, 1, 1)
    layouts = tuple(tuple(1 + int(roots[i] == r) + int(i == j) for i in range(5))
                    for r in range(2) for j in range(5))
    require(type(source.ROOT) is tuple and all(type(x) is int for x in source.ROOT)
            and source.ROOT == roots and source.BASES == layouts
            and all(type(x) is int for b in source.BASES for x in b), 'Ten original shallow layouts')
    pairs = [(0, 0), (0, 1), (0, 2), (1, 0), (2, 0)]
    given = inputs['quadratic_constants']
    require(isinstance(given, list) and len(given) == 5, 'Exactly five quadratic costs')
    G = _rational(inputs['source_square_bound'])
    require(max(F(5273, 258), F(14543, 438)) < G < F(consumer['source_G357']),
            'Source improves while covering both missing-class branches')
    specs = [(None, G)]
    for pair, row in zip(pairs, given):
        require(set(row) == {'tuple', 'constant'} and type(row['tuple']) is list
                and len(row['tuple']) == 2 and all(type(x) is int for x in row['tuple'])
                and row['tuple'] == list(pair), 'Original AP tuple identity and order')
        specs.append((pair, _rational(row['constant'])))
    blocks, outside = source.ap_original_block_inputs(source.CAP13, 4, 2)
    require([p for p, _, _, _ in blocks] == pairs and outside >= 0
            and sum(active for _, _, active, _ in blocks) + outside == F(253, 108),
            'Complete degree-two AP complement')
    finite, tails = source.ap_product_distribution(source.CAP13, 4)
    expectation = sum(p * source.zero5_cost(('s', F(16)), n) for n, p in finite.items())
    expectation += tails[2] - 16 * tails[0]
    require(expectation == F(previous['quadratic_cost']['expectation'])
            and outside == F(previous['quadratic_cost']['outside_active_first_moment']),
            'Rebuilt complete AP expectation and complement')
    H16 = expectation + sum(C for _, C in specs[1:]) + outside * (G - 1)
    H41 = F(previous['H']['joint'])
    oldG = F(consumer['source_G357'])
    require(oldG == F(previous['source_G357']) == F(765767, 21465), 'Same predecessor source')
    require(H16 < F(previous['H16']), 'Strict complete quadratic improvement')

    @lru_cache(None)
    def distance(eta, b, c):
        delta = tuple(x - y for x, y in zip(b, c))
        return sum(w * x * x for w, x in zip(eta, delta)) - (
            max((0,) + delta) ** 2 + max((0,) + tuple(-x for x in delta)) ** 2) / F(18)

    entries = []
    for pair, C in specs:
        tag, zero, psi, mean, curve = _psi_record(source, pair)
        bases = []
        for b in layouts:
            fb = tuple(source.zero5_cost(tag, x) for x in b)
            inc = tuple(source.zero5_cost(tag, x + 1) - v for x, v in zip(b, fb))
            require(C >= source.zero5_cost(tag, 4), 'Final norm exceeds the actual four-load cost')
            # Each baseline's full depth tail is precomputed below, by scalar b.
            bases.append((b, fb, inc,tuple(psi(x) for x in b),
                          tuple(source.zero5_centered_correction(zero, x) for x in b)))
        z0, z1, _ = source.geom(3, 4)
        deep = {b: (psi(2 * (b + 1)) - psi(2 * b)) / 27
                   + 4 * mean * (2 * z1 + (2 * b - 5) * z0) for b in (1, 2, 3)}
        entries.append({'pair': pair, 'C': C, 'tag': tag, 'zero': zero, 'psi': psi,
                        'curve': curve, 'mean': mean, 'deep': deep, 'bases': bases})

    @lru_cache(None)
    def savings(ci, li, eta):
        item = entries[ci]
        b = layouts[li]
        raw = tuple(sum(eta[j] * item['psi'](2 * c[j]) for j in range(5))
                    + max(item['deep'][x] for x in c) for c in layouts)
        coupled = tuple(value - 2 * item['curve'] * distance(eta, b, c)
                        for value, c in zip(raw, layouts))
        require(all(distance(eta, b, c) >= 0 for c in layouts), 'Affine distance on every width vertex')
        require(all(value == source.zero5_scaled_pure(item['zero'], 2, c, eta)
                    for value, c in zip(raw, layouts)), 'Independent full pure3 cost tail')
        saving = F(2, 25) * (max(raw) - max(coupled))
        require(saving >= 0, 'Coupled maximum improves the same N5=2 term')
        return saving

    parameters = list(source.vertices())
    require(len(parameters) == len(consumer['rows']) == 1296, 'Complete parameter domain')
    minima, zeros = [None] * 6, [[] for _ in range(6)]
    digests = [sha256() for _ in range(6)]
    results = []
    coef81 = G * source.TAIL81_2 - 81 * source.TAIL81_0 + sum(
        p * n * n * (G - 1) for n, p in source.PR81.items() if n in source.CAP81_N)
    for index, par in enumerate(parameters):
        dat = source.data(par)
        d, mass, eta, s, D = dat
        delta = source.delta(dat)
        saved = consumer['rows'][index]
        require(type(saved['index']) is int and saved['index'] == index
                and saved['parameters'] == encode(par)
                and F(saved['D']) == D and F(saved['Delta']) == delta > 0,
                'Unchanged actual source parameters and full-tail AP survival')
        for ci, item in enumerate(entries):
            tag, zero, C = item['tag'], item['zero'], item['C']
            # The removed zero7 maximum is exactly the selected summand.
            remainder = (source.zero7_raw(tag, dat) - source.zero5_raw(zero, dat)
                         + source.zero5_positive_with_constant(zero, eta))
            for li, (b, fb, inc, psi_values, correction) in enumerate(item['bases']):
                selected = remainder + sum(mass[j] * psi_values[j] + eta[j] * correction[j]
                                           for j in range(5))
                selected += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
                selected -= savings(ci, li, eta)
                margin = C * s - selected - _cofactor_cap(source, dat, C, fb, inc) / 5
                require(margin >= 0, 'Final norm margin: ' + str((index, ci, li)))
                minima[ci] = margin if minima[ci] is None else min(minima[ci], margin)
                if margin == 0:
                    zeros[ci].append([index, li])
                digests[ci].update(json.dumps([index, li, str(margin)], separators=(',', ':')).encode() + b'\n')
        u81 = coef81 * D + sum(p * n * n * source.square357(F(81, n * n), dat)
                              for n, p in source.PR81.items() if n not in source.CAP81_N)
        results.append({'index': index, 'D': D, 'Delta': delta, 'U81': u81,
                        'Gamma13': 16 + D * H16 / delta, 'T81': u81 / delta,
                        'joint': source.WHOLE_CONST + D * (source.AC * H16 + H41) / delta})
        if progress is not None:
            progress(index + 1, 1296)
    require(minima == [F(0)] * 6, 'All six exact fixed norms have active witnesses')
    targets = {key: max(row[key] for row in results) for key in ('Gamma13', 'T81', 'joint')}
    coefficients = {'Gamma13': (targets['Gamma13'] - 16) * F(131, 132) - H16,
                    'T81': targets['T81'] * F(131, 132) - coef81,
                    'joint': (targets['joint'] - source.WHOLE_CONST) * F(131, 132)
                             - source.AC * H16 - H41}
    require(min(coefficients.values()) > 0, 'Every continuous-domain extension coefficient')
    fallbacks = []
    for name, pure, density in source.FALLBACK_INPUTS:
        caps = tuple((p, 1 / u) for p, u in zip((3, 5, 7), pure))
        factor = density * prod(pure)
        hs = {h: factor * source.product_hinge(caps, F(h)) for h in (3, 4, 6)}
        survival = F(131, 132) - hs[4] / 6 - F(14, 99) * hs[6] - F(7, 132) * hs[3]
        require(survival > 0, 'Actual missing-class survival')
        sq = lambda t: factor * source.product_square_hinge(caps, t)
        u16 = G * source.TAIL2 - 16 * source.TAIL0 + sum(
            p * n * n * min(sq(F(16, n * n)), G - 1) for n, p in source.PR16.items())
        u81 = G * source.TAIL81_2 - 81 * source.TAIL81_0 + sum(
            p * n * n * min(sq(F(81, n * n)), G - 1) for n, p in source.PR81.items())
        hinge = {h: factor * source.product_hinge(caps + source.CAP13, F(h)) / survival
                 for h in (5, 6, 7, 8)}
        joint = source.WHOLE_CONST + source.AC * (targets['Gamma13'] - 16)
        joint += sum(c * hinge[h] for h, c in source.WEIGHT17)
        joint += source.P17 * sum(c * hinge[h] for h, c in source.WEIGHT19) + source.EXTRA5 * hinge[5]
        row = {'branch': name, 'Gamma13': 16 + u16 / survival, 'T81': u81 / survival, 'joint': joint}
        require(all(row[key] <= targets[key] for key in targets), 'Complete missing-class consumer')
        fallbacks.append(row)
    require(len(fallbacks) == 8 and len({row['branch'] for row in fallbacks}) == 8,
            'Eight distinct complete missing-class branches')
    require(targets['joint'] < F(previous['bound']) and targets['Gamma13'] < F(consumer['Gamma13'])
            and targets['T81'] < F(consumer['T13_81']), 'All three stated improvements')
    require(F(consumer['frontier_box20']) == 403 - F(consumer['T13_81']) - F(667, 1000000)
            and F(consumer['frontier_unequal']) == 403 - F(consumer['T13_81']) - F(263, 1000),
            'Same-law complete finite-core error allowances')
    allowance = 403 - targets['T81'] - F(667, 1000000)
    return encode({'schema': 'erdos7-layout-gap-frontier-v1', 'source_G357': G,
                   'H16': H16, 'H41': H41, 'bound': targets['joint'], 'Gamma13': targets['Gamma13'],
                   'T13_81': targets['T81'], 'frontier_box20': allowance,
                   'frontier_unequal': 403 - targets['T81'] - F(263, 1000),
                   'remaining_gap': targets['joint'] - allowance,
                   'source_square_margin_checks': 12960, 'quadratic_margin_checks': 64800,
                   'consumer_vertex_checks': 1296, 'fallback_checks': 8,
                   'continuous_coefficients': coefficients,
                   'norms': [{'tuple': item['pair'], 'C': item['C'], 'curve': item['curve'],
                             'minimum_margin': minima[i], 'zero_margins': zeros[i],
                             'margin_sha256': digests[i].hexdigest()} for i, item in enumerate(entries)],
                   'maximizers': {key: [r['index'] for r in results if r[key] == targets[key]]
                                  for key in targets}, 'other_eight_branches': fallbacks,
                   'scope': 'Original labels and complete tails on unchanged actual AP(4,6). Ordinary Jensen/distance proof with exact arithmetic; no Lean or unrestricted conclusion.'})
