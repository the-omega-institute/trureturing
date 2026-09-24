"""Exact fixed-cost component for the original-label joint frontier.

The public API is reconstruct(source, consumer, norm_inputs, progress=None).
The source object supplies the existing joint verifier's mathematical API;
consumer is its checked six-cofactor certificate. No discovery history,
point-dependent norm roots, IO, or source-global mutation occurs here.
All final constants are checked directly at every vertex and layout.
"""
from fractions import Fraction as F
from math import prod

MODES = ('floor', 'joint')


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


def _inventory(source, inputs):
    require(isinstance(inputs, dict) and set(inputs) == {
        'schema', 'source_square_bound', 'constants', 'quadratic_constants'},
        'Exact fixed-cost input fields')
    require(inputs['schema'] == 'erdos7-fixed-cost-norm-input-v2',
            'Fixed-cost input schema')
    require(source.ROOT == (0, 0, 1, 1, 1)
            and all(type(value) is int for value in source.ROOT),
            'Original five-cell source domain')
    expected_bases = tuple(tuple(1 + int(source.ROOT[i] == r) + int(i == j)
                                 for i in range(5))
                           for r in range(2) for j in range(5))
    require(source.BASES == expected_bases
            and all(type(value) is int for row in source.BASES for value in row),
            'Exact ten original layouts and their order')
    rows, quadratic_rows = inputs['constants'], inputs['quadratic_constants']
    require(isinstance(rows, list) and len(rows) == 41,
            'Forty finite AP costs and one complete linear direction')
    require(isinstance(quadratic_rows, list) and len(quadratic_rows) == 5,
            'Exactly five quadratic AP costs')
    specs, groups = [], []
    for name, weights in (('R17', source.WEIGHT17),
                          ('R19', source.WEIGHT19), ('R5', source.W5)):
        tag = ('w', (weights, 1))
        degree, leading, _, cutoff = source.zero5_cost_metadata(tag)
        require(degree == 1 and leading >= 0, 'Nonnegative affine parent cost')
        blocks, outside = source.ap_original_block_inputs(source.CAP13, cutoff, degree)
        require(len(blocks) == (8 if name == 'R5' else 16), 'Finite AP inventory')
        require(outside >= 0 and
                sum(active for _, _, active, _ in blocks) + outside == F(49, 36),
                'Complete active AP tuple first moment')
        indices = []
        for (e, f), _, _, _ in blocks:
            indices.append(len(specs))
            specs.append({'name': name, 'tuple': [e, f],
                          'tag': ('ap_block', (tag, source.CAP13, e, f))})
        groups.append({'name': name, 'cutoff': cutoff, 'indices': indices,
                       'expectation': source.w_ap_base(weights, source.CAP13),
                       'tail_coefficient': leading * outside,
                       'outside_active_mass': outside})
    specs.append({'name': 'linear', 'tuple': None, 'tag': ('h', F(0))})
    for spec in specs:
        spec['modes'], spec['cofactor_count'] = MODES, 5
    tag = ('s', F(16))
    degree, leading, constant, cutoff = source.zero5_cost_metadata(tag)
    require((degree, leading, constant, cutoff) == (2, 1, -16, 4),
            'Quadratic anchor16 parent cost')
    blocks, outside = source.ap_original_block_inputs(source.CAP13, cutoff, degree)
    require([pair for pair, _, _, _ in blocks] == [(0, 0), (0, 1), (0, 2), (1, 0), (2, 0)],
            'Exact five exceptional quadratic tuples')
    require(outside >= 0 and sum(active for _, _, active, _ in blocks) + outside
            == source.moment(source.CAP13, 2) == F(253, 108),
            'Complete quadratic AP second moment')
    finite, tails = source.ap_product_distribution(source.CAP13, cutoff)
    expectation = sum(prob * source.zero5_cost(tag, n) for n, prob in finite.items())
    expectation += leading * tails[2] + constant * tails[0]
    quadratic = {'name': 'H16', 'threshold': 16, 'indices': [],
                 'expectation': expectation, 'tail_coefficient': leading * outside,
                 'outside_active_first_moment': outside}
    for (e, f), _, _, _ in blocks:
        quadratic['indices'].append(len(specs))
        specs.append({'name': 'H16', 'tuple': [e, f],
                      'tag': ('ap_block', (tag, source.CAP13, e, f)),
                      'modes': ('joint',), 'cofactor_count': 6})
    for spec, row in zip(specs, rows + quadratic_rows):
        require(isinstance(row, dict) and set(row) == {'name', 'tuple', *spec['modes']},
                'Norm input fields')
        require(row['tuple'] is None if spec['tuple'] is None
                else isinstance(row['tuple'], list) and len(row['tuple']) == 2
                and all(type(value) is int for value in row['tuple']),
                'Exact nonnegative integer AP tuple encoding')
        require((row['name'], row['tuple']) == (spec['name'], spec['tuple']),
                'Fixed norm identity and complete tuple order')
        for mode in spec['modes']:
            require(isinstance(row[mode], str), 'Rational constants encoded as strings')
            spec[mode] = F(row[mode])
            require(str(spec[mode]) == row[mode], 'Canonical exact rational constant')
        _prepare_layouts(source, spec)
    return specs, groups, quadratic


def _prepare_layouts(source, spec):
    tag = spec['tag']
    spec['four_load_cost'] = source.zero5_cost(tag, F(4))
    require(spec['joint'] >= spec['four_load_cost'] >= 0,
            'Final constant supports the unclipped four-load floor')
    require('floor' not in spec or spec['floor'] >= spec['joint'],
            'Floor comparison dominates the same-event constant')
    zero = ('seven_block', (tag, 0))
    spec['zero'], spec['layouts'] = zero, []
    for baseline in source.BASES:
        fb = tuple(source.zero5_cost(tag, F(b)) for b in baseline)
        fc = tuple(source.zero5_cost(tag, F(b + 1)) for b in baseline)
        layout = {'baseline': baseline,
                  'psi': tuple(source.zero5_cost(zero, F(b)) for b in baseline),
                  'correction': tuple(source.zero5_centered_correction(zero, F(b))
                                      for b in baseline)}
        for mode in spec['modes']:
            k = tuple(spec[mode] - v for v in fb)
            c = tuple(v - u for u, v in zip(fb, fc)) if mode == 'joint' else (F(0),) * 5
            require(all(0 <= v <= u for u, v in zip(k, c)), 'Exact cost floor')
            layout[mode] = (k, c)
        spec['layouts'].append(layout)
    spec['minimum_margin'] = {mode: None for mode in spec['modes']}
    spec['first_minimizer'] = {mode: None for mode in spec['modes']}
    spec['minimizer_count'] = {mode: 0 for mode in spec['modes']}


def _cofactor_cap(dat, k, c, cofactor_count=5):
    require(type(cofactor_count) is int and cofactor_count in (5, 6),
            'Supported actual-cofactor count')
    selected, tail = ((F(13, 243), F(1, 486)) if cofactor_count == 5
                      else (F(40, 729), F(1, 1458)))
    require(selected + tail == F(1, 18), 'Complete pure3 deep complement')
    d, n, eta, _, _ = dat
    w = tuple(9 * v for v in eta)
    signed = tuple(k[l] * n[l] - c[l] * eta[l] / 5 for l in range(5))
    require(sum(signed) >= 0, 'Empty original root and cell alternatives')
    deep = tuple(k[l] * d[l] - c[l] / 5 for l in range(5))
    require(min(deep) >= 0, 'Every deep signed cylinder coefficient')
    kw = tuple(k[l] * w[l] for l in range(5))
    rootmax = lambda values: max(sum(values[:2]), sum(values[2:]))
    return (rootmax(signed) + max(signed) + selected * max(deep)
            + tail * max(k[l] * d[l] for l in range(5))
            + (sum(kw) + rootmax(kw) + max(kw)) / 36 + max(k) / 72)


def _record_margin(spec, mode, margin, vertex, layout):
    require(margin >= 0, 'Negative final norm margin: '
            + str((spec['name'], spec['tuple'], mode, vertex, layout, margin)))
    current = spec['minimum_margin'][mode]
    if current is None or margin < current:
        spec['minimum_margin'][mode] = margin
        spec['first_minimizer'][mode] = [vertex, layout]
        spec['minimizer_count'][mode] = 1
    elif margin == current:
        spec['minimizer_count'][mode] += 1


def _fixed_envelopes(specs, groups):
    require(specs[40]['name'] == 'linear', 'Shared linear complement direction')
    for group in groups:
        group['H'] = {
            mode: group['expectation']
                  + sum(specs[i][mode] for i in group['indices'])
                  + group['tail_coefficient'] * (specs[40][mode] - 1)
            for mode in MODES}
        require(group['H']['floor'] >= group['H']['joint'] >= 0,
                'Nonnegative complete probability cost envelope')
    return {mode: groups[0]['H'][mode] + F(15, 17) * groups[1]['H'][mode]
                  + F(13299, 1360) * groups[2]['H'][mode] for mode in MODES}


def _fallbacks(source, consumer, target):
    """Rebuild all eight inherited branches on the same six-source input."""
    G = F(consumer['source_G357'])
    gamma, t81 = F(consumer['Gamma13']), F(consumer['T13_81'])
    inherited = consumer['other_eight_branches']
    require(isinstance(inherited, list) and len(inherited) == 8,
            'Exactly eight inherited branch records')
    supplied = {row['branch']: row for row in inherited}
    expected_names = {name for name, _, _ in source.FALLBACK_INPUTS}
    require(len(supplied) == len(source.FALLBACK_INPUTS) == 8
            and set(supplied) == expected_names, 'Eight distinct inherited branches')
    result = []
    for name, pure, density in source.FALLBACK_INPUTS:
        oldcaps = tuple((p, 1 / mass) for p, mass in zip((3, 5, 7), pure))
        factor = density * prod(pure)
        hs = {h: factor * source.product_hinge(oldcaps, F(h)) for h in (3, 4, 6)}
        survival = F(131, 132) - hs[4] / 6 - F(14, 99) * hs[6] - F(7, 132) * hs[3]
        require(survival > 0, 'Positive inherited branch survival')
        caps = oldcaps + source.CAP13
        hinges = {h: factor * source.product_hinge(caps, F(h)) / survival
                  for h in (5, 6, 7, 8)}
        value = source.WHOLE_CONST + source.AC * (gamma - 16)
        value += sum(c * hinges[h] for h, c in source.WEIGHT17)
        value += source.P17 * sum(c * hinges[h] for h, c in source.WEIGHT19)
        value += source.EXTRA5 * hinges[5]
        square = lambda t: factor * source.product_square_hinge(oldcaps, t)
        u16 = G * source.TAIL2 - 16 * source.TAIL0
        u16 += sum(p * n * n * min(square(F(16, n * n)), G - 1)
                   for n, p in source.PR16.items())
        u81 = G * source.TAIL81_2 - 81 * source.TAIL81_0
        u81 += sum(p * n * n * min(square(F(81, n * n)), G - 1)
                   for n, p in source.PR81.items())
        require(16 + u16 / survival <= gamma and u81 / survival <= t81,
                'Unchanged full-square and threshold81 branch bounds')
        require(value == F(supplied[name]['joint_upper']) <= target,
                'Rebuilt inherited branch below fixed-cost target')
        result.append({'branch': name, 'survival_lower': survival,
                       'joint_upper': value, 'joint_margin': target - value})
    return result


def reconstruct(source, consumer, norm_inputs, progress=None):
    """Return JSON-ready results after direct, exact final-constant checks.

    The C_a bound E_nu357 Q_a on the normalized actual probability.
    D*C_a only forms a numerator for the same probability bound; it
    is never asserted to bound an actual raw integral of mass u>=D.
    The caller owns pinned source verification and certificate IO.
    """
    specs, groups, quadratic = _inventory(source, norm_inputs)
    G = F(norm_inputs['source_square_bound'])
    require(G == F(consumer['source_G357']) == F(765767, 21465),
            'Same six-cofactor source square bound')
    require(source.AC == F(2371, 2880) and source.P17 == F(15, 17)
            and source.EXTRA5 == F(13299, 1360)
            and source.WHOLE_CONST == F(185694867601, 8599322160),
            'Unchanged row-potential consumer')
    dcoef16 = G * source.TAIL2 - 16 * source.TAIL0 + source.PR16[3] * 9 * (G - 1)
    require(dcoef16 == F(consumer['DCOEF16']), 'Rebuilt six-source D coefficient')
    H = _fixed_envelopes(specs, groups)
    H16 = (quadratic['expectation'] + sum(specs[i]['joint'] for i in quadratic['indices'])
           + quadratic['tail_coefficient'] * (G - 1))
    require(H16 >= 0, 'Nonnegative complete quadratic envelope')
    pars = list(source.vertices())
    require(len(pars) == len(consumer['rows']) == 1296, 'All original vertices')
    results, empty_minimum, norm_checks = [], None, 0
    for index, par in enumerate(pars):
        dat = source.data(par)
        d, n, eta, s, D = dat
        x = sum(eta)
        require(min(d) >= F(1, 4) and min(n) >= 0 and D > 0
                and s - x / 5 >= F(5, 36), 'Full domain and empty-branch bound')
        empty_minimum = s - x / 5 if empty_minimum is None else min(empty_minimum, s - x / 5)
        supplied = consumer['rows'][index]
        require(type(supplied['index']) is int and supplied['index'] == index
                and encode(par) == supplied['parameters'] and D == F(supplied['D']),
                'Unchanged parameter point and source mass bound')
        for spec in specs:
            tag, zero = spec['tag'], spec['zero']
            common = (source.zero7_raw(tag, dat) - source.zero5_raw(zero, dat)
                      + source.zero5_positive_with_constant(zero, eta))
            for li, layout in enumerate(spec['layouts']):
                selected = common + sum(n[l] * layout['psi'][l]
                                        + eta[l] * layout['correction'][l] for l in range(5))
                selected += max(source.zero5_common_deep(zero, layout['baseline'][l], d[l])
                                for l in range(5))
                for mode in spec['modes']:
                    k, c = layout[mode]
                    cap = _cofactor_cap(dat, k, c, spec['cofactor_count'])
                    margin = spec[mode] * s - selected - cap / 5
                    _record_margin(spec, mode, margin, index, li)
                    norm_checks += 1
        delta = source.delta(dat)
        require(delta == F(supplied['Delta']) > 0, 'Rebuilt unchanged full-tail survival')
        u16 = dcoef16 * D + sum(p * n * n * source.square357(F(16, n * n), dat)
                               for n, p in source.PR16.items() if n != 3)
        require(u16 == F(supplied['U16']), 'Rebuilt unchanged comparison U16')
        values = {mode: source.WHOLE_CONST + (source.AC * u16 + D * H[mode]) / delta
                  for mode in MODES}
        joint = source.WHOLE_CONST + D * (source.AC * H16 + H['joint']) / delta
        results.append({'index': index, 'D': D, 'Delta': delta,
                        'comparison_U16': u16, 'quadratic_numerator': D * H16,
                        'floor_value': values['floor'], 'linear_joint_value': values['joint'],
                        'joint_value': joint})
        if progress is not None:
            progress(index + 1, len(pars))
    require(norm_checks == 1296 * 10 * (41 * 2 + 5),
            'Every final linear and quadratic norm margin checked directly')
    comparisons = ('floor', 'linear_joint', 'joint')
    targets = {mode: max(row[mode + '_value'] for row in results) for mode in comparisons}
    coefficients = {
        'floor': (targets['floor'] - source.WHOLE_CONST) * F(131, 132)
                 - source.AC * dcoef16 - H['floor'],
        'linear_joint': (targets['linear_joint'] - source.WHOLE_CONST) * F(131, 132)
                        - source.AC * dcoef16 - H['joint'],
        'joint': (targets['joint'] - source.WHOLE_CONST) * F(131, 132)
                 - source.AC * H16 - H['joint']}
    require(min(coefficients.values()) > 0, 'All three continuous-domain extensions')
    old_target = F(consumer['bound'])
    require(targets['joint'] < targets['linear_joint'] < targets['floor'] < old_target,
            'Separate strict improvements at fixed source G')
    for row in results:
        for mode in comparisons:
            u16 = row['quadratic_numerator'] if mode == 'joint' else row['comparison_U16']
            cost = H['floor'] if mode == 'floor' else H['joint']
            numerator = source.AC * u16 + row['D'] * cost
            row[mode + '_margin'] = (targets[mode] - source.WHOLE_CONST) * row['Delta'] - numerator
            require(row[mode + '_margin'] >= 0, 'Whole consumer margin')
    branches = _fallbacks(source, consumer, targets['joint'])
    norm_results = [{key: spec[key] for key in
                     ('name', 'tuple', *spec['modes'], 'cofactor_count', 'four_load_cost',
                      'minimum_margin', 'first_minimizer', 'minimizer_count')}
                    for spec in specs]
    group_results = [{key: group[key] for key in
                      ('name', 'cutoff', 'expectation', 'outside_active_mass',
                       'tail_coefficient', 'H')} | {'finite_tuple_count': len(group['indices'])}
                     for group in groups]
    quadratic_result = {key: quadratic[key] for key in
                        ('name', 'threshold', 'expectation', 'outside_active_first_moment',
                         'tail_coefficient')}
    quadratic_result.update({'finite_tuple_count': 5, 'cofactor_count': 6,
                              'selected_deep_coefficient': F(40, 729),
                              'complete_deep_tail_coefficient': F(1, 1458)})
    return encode({'schema': 'erdos7-fixed-cost-frontier-v2', 'source_G357': G,
                   'bound': targets['joint'], 'linear_joint_bound': targets['linear_joint'],
                   'floor_bound': targets['floor'], 'comparison_bound_same_source': old_target,
                   'floor_gain': old_target - targets['floor'],
                   'additional_same_event_gain': targets['floor'] - targets['linear_joint'],
                   'quadratic_gain': targets['linear_joint'] - targets['joint'],
                   'C0': source.WHOLE_CONST, 'comparison_DCOEF16': dcoef16, 'H': H, 'H16': H16,
                   'continuous_coefficients': coefficients, 'vertex_count': len(pars),
                   'layout_count': 10, 'norm_direction_count': 46,
                   'linear_direction_count': 41, 'quadratic_direction_count': 5,
                   'direct_norm_margin_checks': norm_checks,
                   'minimum_s_minus_x_over5': empty_minimum,
                   'Gamma13': consumer['Gamma13'], 'T13_81': consumer['T13_81'],
                   'frontier_unequal': consumer['frontier_unequal'],
                   'frontier_box20': consumer['frontier_box20'],
                   'maximizers': {mode: [row['index'] for row in results
                                         if row[mode + '_value'] == targets[mode]]
                                  for mode in comparisons},
                   'costs': group_results, 'quadratic_cost': quadratic_result,
                   'norm_checks': norm_results[:41], 'quadratic_norm_checks': norm_results[41:],
                   'other_eight_branches': branches, 'rows': results,
                   'scope': 'Exact arithmetic for the ordinary actual-probability proof; five cofactors for linear costs, six for quadratic costs, all original labels and tails. Gamma13 and T13_81 are inherited unchanged. No Lean or unrestricted resolution claim.'})
