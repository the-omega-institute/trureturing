"""Final norms and complete consumers for the actual AP(4,5) law.

No discovery roots, finite-height truncation, or source-global mutation.
The caller supplies pinned mathematical modules and predecessor inputs.
"""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import json

CAPS = ((11, F(5, 3)), (13, F(12, 7)))
QD = F(919, 924)
PAIRS = ((0, 0), (0, 1), (0, 2), (1, 0), (2, 0))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    require(type(value) is str, 'Rational input is a string')
    result = F(value)
    require(str(result) == value, 'Canonical rational input')
    return result


def inventory(source, fixed, inputs):
    require(type(inputs) is dict and set(inputs) == {
        'schema', 'source_square_bound', 'constants', 'quadratic_constants'}, 'Exact norm input fields')
    require(inputs['schema'] == 'erdos7-ap45-layout-norm-input-v1', 'New-law norm schema')
    require(source.ROOT == (0, 0, 1, 1, 1) and all(type(x) is int for x in source.ROOT),
            'Original five-cell source domain')
    layouts = tuple(tuple(1 + int(source.ROOT[i] == r) + int(i == j) for i in range(5))
                    for r in range(2) for j in range(5))
    require(source.BASES == layouts and all(type(v) is int for b in source.BASES for v in b),
            'Exact ten original layouts')
    require(source.AC == F(2371, 2880) and source.P17 == F(15, 17)
            and source.EXTRA5 == F(13299, 1360)
            and source.WHOLE_CONST == F(185694867601, 8599322160), 'Unchanged later row potential')
    require(type(inputs['constants']) is list and len(inputs['constants']) == 41
            and type(inputs['quadratic_constants']) is list and len(inputs['quadratic_constants']) == 5,
            'All forty-one linear and five quadratic directions')
    specs, groups = [], []
    for name, weights in (('R17', source.WEIGHT17), ('R19', source.WEIGHT19), ('R5', source.W5)):
        tag = ('w', (weights, 1))
        degree, leading, _, cutoff = source.zero5_cost_metadata(tag)
        blocks, outside = source.ap_original_block_inputs(CAPS, cutoff, degree)
        require(degree == 1 and leading >= 0 and len(blocks) == (8 if name == 'R5' else 16)
                and outside >= 0 and sum(active for _, _, active, _ in blocks) + outside == F(4, 3),
                'Complete new-law linear tuple inventory and full first moment')
        indices = []
        for (e, f), _, _, _ in blocks:
            indices.append(len(specs))
            specs.append({'name': name, 'tuple': [e, f], 'tag': ('ap_block', (tag, CAPS, e, f)),
                          'modes': ('joint',), 'cofactor_count': 5})
        groups.append({'name': name, 'indices': indices, 'finite_tuple_count': len(blocks),
                       'expectation': source.w_ap_base(weights, CAPS),
                       'outside_active_mass': outside, 'tail_coefficient': leading * outside})
    specs.append({'name': 'linear', 'tuple': None, 'tag': ('h', F(0)),
                  'modes': ('joint',), 'cofactor_count': 5})
    blocks, outside = source.ap_original_block_inputs(CAPS, 4, 2)
    require(tuple(pair for pair, _, _, _ in blocks) == PAIRS and outside >= 0
            and sum(active for _, _, active, _ in blocks) + outside == F(1403, 630),
            'All five quadratic tuples and complete new-law second moment')
    for e, f in PAIRS:
        specs.append({'name': 'H16', 'tuple': [e, f], 'tag': ('ap_block', (('s', F(16)), CAPS, e, f)),
                      'modes': ('joint',), 'cofactor_count': 6})
    for spec, row in zip(specs, inputs['constants'] + inputs['quadratic_constants']):
        require(type(row) is dict and set(row) == {'name', 'tuple', 'constant'}, 'Exact norm row fields')
        require(row['tuple'] is None if spec['tuple'] is None else type(row['tuple']) is list
                and len(row['tuple']) == 2 and all(type(v) is int for v in row['tuple']), 'Original tuple encoding')
        require((row['name'], row['tuple']) == (spec['name'], spec['tuple']), 'Original norm identity and order')
        spec['joint'] = rational(row['constant'])
        fixed._prepare_layouts(source, spec)
    finite, tails = source.ap_product_distribution(CAPS, 4)
    expectation = sum(p * source.zero5_cost(('s', F(16)), n) for n, p in finite.items())
    expectation += tails[2] - 16 * tails[0]
    return specs, groups, {'expectation': expectation, 'outside_active_first_moment': outside}


def psi_record(source, layout, pair):
    """Entire new-cap zero7 cost from complete first moment and K<4 atoms."""
    e, f = pair
    zero = ('seven_block', (('ap_block', (('s', F(16)), CAPS, e, f)), 0))
    mean = F(6, 5) * layout._active_first(11, F(5, 3), e) * layout._active_first(13, F(12, 7), f)
    atoms = {k: sum((F(29, 35) if n7 == 1 else F(36, 5 * 7 ** n7))
                   * layout._probability(11, F(5, 3), n11) * layout._probability(13, F(12, 7), n13)
                   for n7 in range(1, k + 1) for n11 in range(1, k + 1) for n13 in range(1, k + 1)
                   if n7 * n11 * n13 == k and n11 > e and n13 > f) for k in range(1, 4)}

    def psi(v):
        return mean * (v * v - 1) + sum(F(p) / k * (
            max(F(16 - k * k * v * v), F(0)) - (16 - k * k)) for k, p in atoms.items())

    curve = min((psi(k + 1) - 2 * psi(k) + psi(k - 1)) / 2 for k in range(2, 6))
    degree, leading, constant, cutoff = source.zero5_cost_metadata(zero)
    require(degree == 2 and leading == mean and cutoff <= 4 and constant == psi(4) - 16 * mean,
            'Exact new-cap quadratic tail')
    require(curve > 0 and (psi(6) - 2 * psi(5) + psi(4)) / 2 == mean
            and all(source.zero5_cost(zero, v) == psi(v) for v in range(1, 7)),
            'Independent new-cap curvature and every pre-tail value')
    z0, z1, _ = source.geom(3, 4)
    deep = {b: (psi(2 * (b + 1)) - psi(2 * b)) / 27
               + 4 * mean * (2 * z1 + (2 * b - 5) * z0) for b in (1, 2, 3)}
    return zero, psi, curve, deep, {'tuple': pair, 'mean': mean, 'curvature': curve, 'low_product_atoms': atoms}


def reconstruct(source, fixed, layout, core, kc, previous, pure, inputs, progress=None):
    specs, groups, quadratic = inventory(source, fixed, inputs)
    G = rational(inputs['source_square_bound'])
    require(G == F(previous['source_G357']) == F(1730443, 48600)
            and previous['source_square_margin_checks'] == 12960, 'Retained original-layout source-square bound')
    psis = [psi_record(source, layout, pair) for pair in PAIRS]

    @lru_cache(None)
    def gap(ci, li, eta):
        zero, psi, curve, deep, _ = psis[ci]
        baseline = source.BASES[li]
        raw = tuple(sum(w * psi(2 * v) for w, v in zip(eta, b)) + max(deep[v] for v in b)
                    for b in source.BASES)
        require(all(v == source.zero5_scaled_pure(zero, 2, b, eta)
                    for b, v in zip(source.BASES, raw)), 'Independent complete pure3 depth tail')
        ds = []
        for b in source.BASES:
            delta = tuple(x - y for x, y in zip(baseline, b))
            ds.append(sum(w * v * v for w, v in zip(eta, delta)) - (
                max((0,) + delta) ** 2 + max((0,) + tuple(-v for v in delta)) ** 2) / F(18))
        require(min(ds) >= 0, 'Affine layout-distance lower bound')
        value = F(2, 25) * (max(raw) - max(v - 2 * curve * d for v, d in zip(raw, ds)))
        require(value >= 0, 'Coupled N5=2 replacement')
        return value

    for group in groups:
        group['H'] = group['expectation'] + sum(specs[i]['joint'] for i in group['indices'])
        group['H'] += group['tail_coefficient'] * (specs[40]['joint'] - 1)
    H41 = groups[0]['H'] + source.P17 * groups[1]['H'] + source.EXTRA5 * groups[2]['H']
    H16 = quadratic['expectation'] + sum(s['joint'] for s in specs[41:])
    H16 += quadratic['outside_active_first_moment'] * (G - 1)
    finite, tails = source.ap_product_distribution(CAPS, 9)
    dcoef = G * tails[2] - 81 * tails[0] + sum(p * n * n * (G - 1) for n, p in finite.items() if n in (7, 8))
    pars = list(source.vertices())
    require(len(pars) == 1296, 'Complete parameter domain')
    rows, checks, digest = [], 0, sha256()
    for index, par in enumerate(pars):
        dat = source.data(par)
        d, mass, eta, s, D = dat
        require(min(d) >= F(1, 4) and min(mass) >= 0 and D > 0
                and s - sum(eta) / 5 >= F(5, 36), 'Full domain and empty alternatives')
        for ci, spec in enumerate(specs):
            tag, zero = spec['tag'], spec['zero']
            common = source.zero7_raw(tag, dat) - source.zero5_raw(zero, dat)
            common += source.zero5_positive_with_constant(zero, eta)
            for li, item in enumerate(spec['layouts']):
                selected = common + sum(mass[j] * item['psi'][j] + eta[j] * item['correction'][j] for j in range(5))
                selected += max(source.zero5_common_deep(zero, item['baseline'][j], d[j]) for j in range(5))
                if ci >= 41:
                    selected -= gap(ci - 41, li, eta)
                k, c = item['joint']
                margin = spec['joint'] * s - selected - fixed._cofactor_cap(dat, k, c, spec['cofactor_count']) / 5
                fixed._record_margin(spec, 'joint', margin, index, li)
                digest.update(json.dumps([index, ci, li, str(margin)], separators=(',', ':')).encode() + b'\n')
                checks += 1
        delta = QD * D - source.raw357(F(4), dat) / 6
        delta -= F(4, 33) * source.raw357(F(5), dat) + source.raw357(F(5, 2), dat) / 22
        require(delta > 0, 'New-law full-tail survival')
        U = dcoef * D + sum(p * n * n * source.square357(F(81, n * n), dat)
                           for n, p in finite.items() if n not in (7, 8))
        rows.append({'index': index, 'D': D, 'Delta': delta, 'rho': delta / D,
                     'Gamma13': 16 + D * H16 / delta, 'T13_81': U / delta,
                     'bound': source.WHOLE_CONST + D * (source.AC * H16 + H41) / delta})
        if progress is not None:
            progress(index + 1, len(pars))
    require(checks == 596160, 'All forty-six final norm margins')
    targets = {key: max(row[key] for row in rows) for key in ('bound', 'Gamma13', 'T13_81')}
    rho = min(row['rho'] for row in rows)
    coefficients = {'bound': (targets['bound'] - source.WHOLE_CONST) * QD - source.AC * H16 - H41,
                    'Gamma13': (targets['Gamma13'] - 16) * QD - H16,
                    'T13_81': targets['T13_81'] * QD - dcoef, 'survival': QD - rho}
    require(min(coefficients.values()) > 0, 'Every continuous-domain extension coefficient')
    branches, rho = core.fallbacks(source, CAPS, G, targets, rho)
    source_inputs, errors = core.core_errors(kc, pure['source_inputs'], targets['Gamma13'], rho,
                                           targets['T13_81'], targets['bound'])
    require(targets['bound'] < F(previous['bound']) and targets['T13_81'] < F(previous['T13_81']),
            'Strict target and threshold81 improvement over AP(4,6)')
    norm_results = [{key: spec[key] for key in ('name', 'tuple', 'joint', 'cofactor_count',
                    'four_load_cost', 'minimum_margin', 'first_minimizer', 'minimizer_count')} for spec in specs]
    row_digest = sha256(json.dumps(fixed.encode(rows), sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return fixed.encode({'schema': 'erdos7-ap45-layout-frontier-v1', 'physical_thresholds': [4, 5], 'caps': CAPS,
                         'source_G357': G, 'H41': H41, 'H16': H16, **targets,
                         'continuous_coefficients': coefficients, 'source_inputs': source_inputs,
                         'vertex_count': len(rows), 'layout_count': 10, 'norm_direction_count': 46,
                         'direct_norm_margin_checks': checks, 'norm_margin_sha256': digest.hexdigest(),
                         'consumer_row_sha256': row_digest, 'quadratic_cost': quadratic,
                         'linear_costs': [{k: v for k, v in group.items() if k != 'indices'} for group in groups],
                         'curvatures': [record[-1] for record in psis], 'norms': norm_results,
                         'maximizers': {key: [r['index'] for r in rows if r[key] == value] for key, value in targets.items()},
                         'other_eight_branches': branches, 'core_errors': errors,
                         'scope': 'Actual AP(4,5) throughout; independent original residues, complete source and physical/killed/test tails. Ordinary proof and exact arithmetic. Negative Q, later-prime continuation and unrestricted Erdős7 remain open; no Lean endpoint.'})
