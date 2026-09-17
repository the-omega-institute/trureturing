"""Exact finite consumer of ML observation §46, conditional on RRO §34 geometry.

The cycle model checks linear consequences, not a general split-prefix codec.
Only the four explicitly cited endpoints below use actual digit fixtures.
Called by finite_checks.py; no RNG, global counters, or second entry point.
"""
from fractions import Fraction as F
import hashlib
from itertools import product
from pathlib import Path


def boundary_count(depth):
    assert isinstance(depth, int) and depth >= 0
    a, b = 1, 2
    for _ in range(depth):
        a, b = b, a + b
    return a if depth else 0


def retention_parameters(schedule):
    assert schedule
    bounds = tuple(boundary_count(depth) for depth in schedule)
    future = max([0] + [bound - n for n, bound in enumerate(bounds) if n])
    dimension = max(bounds[0], future)
    rank = dimension if future else max(0, dimension - 1)
    return bounds[0], future, dimension, rank


def cycle_columns(order):
    """Columns are indexed by geometric label, rows by oriented circle arc."""
    size = len(order)
    assert size >= 2 and sorted(order) == list(range(1, size + 1))
    columns = [[F(0)] * size for _ in order]
    for arc, label in enumerate(order):
        columns[label - 1][arc] += 1
        columns[label - 1][(arc - 1) % size] -= 1
    return tuple(tuple(column) for column in columns)


def residual_matrix(schedule, orders, dimension):
    assert dimension >= 0
    rows = []
    for n, depth in enumerate(schedule):
        bound = boundary_count(depth)
        if bound == 0:
            rows.append(tuple(F(0) for _ in range(dimension)))
            continue
        columns = cycle_columns(orders[bound])
        for arc in range(bound):
            rows.append(tuple(columns[k + n][arc] if k + n < bound else F(0)
                              for k in range(dimension)))
    return tuple(rows)


def exact_rank(rows, width):
    """Rational elimination, including explicitly shaped 0-by-width matrices."""
    assert width >= 0 and all(len(row) == width for row in rows)
    matrix = [[F(value) for value in row] for row in rows]
    pivot_row = 0
    for column in range(width):
        pivot = next((i for i in range(pivot_row, len(matrix))
                      if matrix[i][column]), None)
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        divisor = matrix[pivot_row][column]
        matrix[pivot_row] = [value / divisor for value in matrix[pivot_row]]
        for i in range(pivot_row + 1, len(matrix)):
            factor = matrix[i][column]
            matrix[i] = [x - factor * y for x, y in zip(matrix[i], matrix[pivot_row])]
        pivot_row += 1
    return pivot_row


def shifted_residual(g, steps):
    assert steps >= 0
    current = {k: value for k, value in enumerate(g, 1)}
    for _ in range(steps):
        current = {k + 1: value for k, value in current.items()}
    return current


def scatter_residual(g, schedule, orders):
    """Independent update-and-scatter evaluation, without building the matrix."""
    output = []
    for n, depth in enumerate(schedule):
        bound = boundary_count(depth)
        histogram = [F(0)] * max(1, bound)
        if bound:
            order = orders[bound]
            for label, value in shifted_residual(g, n).items():
                if label <= bound:
                    following = order.index(label)
                    histogram[following] += value
                    histogram[(following - 1) % bound] -= value
        output.extend(histogram)
    return tuple(output)


def probability_histograms(g, schedule, orders):
    """Equal phase atoms, endpoint masses g_k and 1/K-g_k in the cycle model.

    Off-boundary pairs share arc zero by convention. This is conditional
    incidence data at each requested depth, not mutually nested RRO cylinders.
    At K=0 a fixed residual-free probability has mass one in that arc.
    """
    dimension = len(g)
    weight = F(1, dimension) if dimension else F(1)
    assert all(0 <= value <= weight for value in g)
    output = []
    for n, depth in enumerate(schedule):
        bound = boundary_count(depth)
        histogram = [F(0)] * max(1, bound)
        for k, value in enumerate(g, 1):
            if bound and k + n <= bound:
                plus = orders[bound].index(k + n)
                minus = (plus - 1) % bound
            else:
                plus = minus = 0
            histogram[plus] += value
            histogram[minus] += weight - value
        if not dimension:
            histogram[0] = F(1)
        assert sum(histogram) == 1 and min(histogram) >= 0
        output.extend(histogram)
    return tuple(output)


def linear_code(g, future):
    return tuple(g) if future else tuple(value - g[-1] for value in g[:-1])


def decode_residual(code, schedule, orders):
    _, future, dimension, rank = retention_parameters(schedule)
    assert len(code) == rank
    representative = tuple(code) if future or not dimension else (*code, F(0))
    return scatter_residual(representative, schedule, orders)


def endpoint_prefix(index, sign, depth):
    """Only m=1..4, L=0..2, from RRO 20.2's oriented word formula."""
    assert index in (1, 2, 3, 4) and sign in ('-', '+') and 0 <= depth <= 2
    v = (0, 1) * 3
    if index == 1:
        pair = (v, (1, 0) * 3)
    else:
        word = {2: (), 3: (0,), 4: (1, 0)}[index]
        length = len(word)
        weights = (1, 2, 3, 5)
        assert weights[length + 1] - sum(weights[j] * digit
                                         for j, digit in enumerate(word)) == index
        first, second = word + (1, 0) + v, word + (0,) + v
        pair = (first, second) if length % 2 == 0 else (second, first)
    return pair[sign == '+'][:depth]


def endpoint_step(index, sign, steps):
    """Actual deterministic kernel on split support: RRO 25.9/25.12/28.7."""
    assert index >= 1 and sign in ('-', '+') and steps >= 0
    for _ in range(steps):
        # The ordered mixed-sign formula for x_index^- times x_1^+ at tau=0.
        positive_mass = F(1) if sign == '+' else F(0 ** index * (0 - 1),
                                                  0 ** (index + 1) - 1)
        negative_mass = 1 - positive_mass
        assert (positive_mass, negative_mass) in ((1, 0), (0, 1))
        sign = '+' if positive_mass else '-'
        index += 1
    return index, sign


def endpoint_joint(measure, requests):
    assert sum(mass for _, _, mass in measure) == 1
    assert all(mass >= 0 for _, _, mass in measure)
    law = {}
    for index, sign, mass in measure:
        if not mass:
            continue
        record = tuple(endpoint_prefix(*endpoint_step(index, sign, n), depth)
                       for n, depth in requests)
        law[record] = law.get(record, F(0)) + mass
    return law


def endpoint_histogram(measure, time, depth):
    return {record[0]: mass for record, mass in endpoint_joint(measure, ((time, depth),)).items()}


def endpoint_checks(dot, counts):
    half = F(1, 2)
    minus = ((1, '-', half), (2, '-', half))
    plus = ((1, '+', half), (2, '+', half))
    lowest = ((0, 1), (1, 0), (0, 0), (1, 1))
    for index, pair in enumerate(lowest, 1):
        for sign, digit in zip(('-', '+'), pair):
            assert endpoint_prefix(index, sign, 1) == (digit,)
            assert endpoint_step(index, sign, 0) == (index, sign)
            assert endpoint_step(index, sign, 2) == (index + 2, sign)
            counts['rro_actual_endpoint_fixtures'] += 1
    current = {(0,): half, (1,): half}
    assert endpoint_histogram(minus, 0, 1) == endpoint_histogram(plus, 0, 1) == current
    assert endpoint_histogram(minus, 1, 1) == current
    assert endpoint_histogram(plus, 1, 1) == {(0,): F(1)}
    digit_matrix = ((1, -1), (-1, 0))
    stacked_rank = exact_rank(digit_matrix, 2)
    current_rank = exact_rank(digit_matrix[:1], 2)
    assert stacked_rank == 2 and current_rank == 1
    record_order = (((0,), (0,)), ((1,), (0,)), ((0,), (1,)), ((1,), (1,)))
    binary_marginals = set()
    for a, b in product((F(0), F(1, 4), half), repeat=2):
        measure = ((1, '+', a), (1, '-', half - a),
                   (2, '+', b), (2, '-', half - b))
        marginal_ones = []
        for n, row in enumerate(digit_matrix):
            histogram = endpoint_histogram(measure, n, 1)
            assert histogram.get((1,), F(0)) == half + dot(row, (a, b))
            marginal_ones.append(histogram.get((1,), F(0)))
        if a in (0, half) and b in (0, half):
            binary_marginals.add(tuple(marginal_ones))
        joint = endpoint_joint(measure, ((0, 1), (2, 1)))
        assert tuple(joint.get(record, F(0)) for record in record_order) == (half - a, a, b, half - b)
        assert endpoint_histogram(measure, 2, 1) == current
        assert endpoint_histogram(measure, 1, 0) == {(): F(1)}
        counts['rro_actual_probability_box_points'] += 1
    current_classes = len({pair[0] for pair in binary_marginals})
    stacked_classes = len(binary_marginals)
    assert (current_classes, stacked_classes) == (3, 4)
    label_bits = (current_classes - 1).bit_length()
    assert label_bits == (stacked_classes - 1).bit_length() == 2
    minus_joint = endpoint_joint(minus, ((0, 1), (2, 1)))
    plus_joint = endpoint_joint(plus, ((0, 1), (2, 1)))
    joint_l1 = sum(abs(minus_joint.get(key, 0) - plus_joint.get(key, 0)) for key in record_order)
    next_l1 = sum(abs(endpoint_histogram(minus, 1, 1).get(key, 0)
                      - endpoint_histogram(plus, 1, 1).get(key, 0)) for key in current)
    assert joint_l1 == 2 and next_l1 == 1
    counts['rro_actual_joint_counterexamples'] += 1
    # Plan (0,0,2) needs the original first coordinate at current location 3.
    assert retention_parameters((0, 0, 2))[2] == 1
    trace = []
    for sign in ('-', '+'):
        fixed = {1: F(sign == '+')}
        moving = dict(fixed)
        for n in (1, 2):
            fixed = {k + 1: value for k, value in fixed.items() if k + 1 <= 1}
            moving = {k + 1: value for k, value in moving.items()}
            assert moving == {n + 1: F(sign == '+')}
        assert not fixed
        measure = ((1, sign, F(1)),)
        trace.append(endpoint_histogram(measure, 2, 2))
    assert trace == [{(0, 0): F(1)}, {(0, 1): F(1)}]
    counts['rro_moving_window_counterexamples'] += 1
    return {
        'endpoint_fixture': {'citation': 'RRO 20.2 oriented words; 25.9/25.12/28.7 actual kernel',
                             'lowest_digits_minus_plus_m1_to_m4': lowest},
        'current_and_next': {'schedule': [1, 1], 'digit_one_residual_matrix': digit_matrix,
                             'current_rank': current_rank, 'stacked_rank': stacked_rank,
                             'current_binary_classes': current_classes,
                             'stacked_binary_classes': stacked_classes,
                             'fixed_width_bits_in_both_cases': label_bits,
                             'current_minus_and_plus_histogram_01': ['1/2', '1/2'],
                             'next_minus_histogram_01': ['1/2', '1/2'],
                             'next_plus_histogram_01': ['1', '0'],
                             'probability_TV': str(next_l1 / 2), 'signed_variation': str(next_l1)},
        'moving_window': {'schedule': [0, 0, 2], 'initial_cutoff': 1,
                          'needed_current_index_at_time2': 3,
                          'minus_prefix_at_time2': '00', 'plus_prefix_at_time2': '01',
                          'fixed_current_prefix_residual_after_truncation': '0'},
        'joint_boundary': {'schedule': [1, 0, 1], 'record_times': [0, 2],
                            'record_order': ['00', '10', '01', '11'],
                            'minus': [str(minus_joint.get(key, F(0))) for key in record_order],
                            'plus': [str(plus_joint.get(key, F(0))) for key in record_order],
                            'probability_TV': str(joint_l1 / 2), 'signed_variation': str(joint_l1),
                            'phase': '(delta_E1 + delta_E2)/2; a phase measure, not one point'}
    }


def check_rro_retention(dot, canonical):
    """Return scoped result and counts; the entry owner supplies its pure helpers."""
    if not __debug__:
        raise RuntimeError('RRO finite checks require assertions enabled')
    keys = ('schedules', 'schedule_order_cases', 'cycle_order_cases', 'rank_checks',
            'probability_box_points', 'binary_vertices', 'binary_pair_kernel_checks',
            'decoder_checks', 'insufficient_prefix_witnesses', 'tail_column_checks',
            'zero_dimensional_cases', 'actual_endpoint_fixtures',
            'actual_probability_box_points', 'actual_joint_counterexamples',
            'moving_window_counterexamples')
    counts = {'rro_' + key: 0 for key in keys}
    natural = {m: tuple(range(1, m + 1)) for m in (2, 3, 5)}
    permuted = {2: (2, 1), 3: (3, 1, 2), 5: (3, 1, 4, 2, 5)}
    rank_cases = {'future_visible': 0, 'current_only': 0, 'none_visible': 0}
    max_dimension = 0
    for orders in (natural, permuted):
        for size, order in orders.items():
            columns = cycle_columns(order)
            rows = tuple(zip(*columns))
            assert all(sum(row) == 0 for row in rows)
            assert exact_rank(rows, size) == size - 1
            for removed in range(size):
                proper = [row[:removed] + row[removed + 1:] for row in rows]
                assert exact_rank(proper, size - 1) == size - 1
            counts['rro_cycle_order_cases'] += 1
    for horizon in range(3):
        for schedule in product(range(4), repeat=horizon + 1):
            initial, future, dimension, expected_rank = retention_parameters(schedule)
            assert dimension == max([0] + [boundary_count(depth) - n
                                           for n, depth in enumerate(schedule)])
            max_dimension = max(max_dimension, dimension)
            category = 'future_visible' if future else ('current_only' if initial else 'none_visible')
            rank_cases[category] += 1
            counts['rro_schedules'] += 1
            for orders in (natural, permuted):
                matrix = residual_matrix(schedule, orders, dimension)
                assert exact_rank(matrix, dimension) == expected_rank
                counts['rro_rank_checks'] += 1
                if not dimension:
                    assert all(row == () for row in matrix)
                    counts['rro_zero_dimensional_cases'] += 1
                expanded = residual_matrix(schedule, orders, dimension + 2)
                for k in range(dimension, dimension + 2):
                    assert all(row[k] == 0 for row in expanded)
                    counts['rro_tail_column_checks'] += 1
                # Every too-short initial prefix has an actual endpoint Dirac witness
                # under the cited geometry; here check its conditional incidence image.
                for prefix in range(dimension):
                    label = prefix + 1
                    requests = [n for n, depth in enumerate(schedule)
                                if label + n <= boundary_count(depth)]
                    assert requests
                    n = requests[0]
                    size = boundary_count(schedule[n])
                    following = orders[size].index(label + n)
                    positive = tuple(F(i == following) for i in range(size))
                    negative = tuple(F(i == (following - 1) % size) for i in range(size))
                    assert sum(positive) == sum(negative) == 1 and positive != negative
                    g = tuple(F(k == prefix) for k in range(dimension))
                    assert g[:prefix] == (F(0),) * prefix
                    assert any(dot(row, g) for row in matrix)
                    counts['rro_insufficient_prefix_witnesses'] += 1
                weight = F(1, dimension) if dimension else F(1)
                baseline = probability_histograms((F(0),) * dimension, schedule, orders)
                binary_inputs, binary_outputs = [], []
                for levels in product(range(3), repeat=dimension):
                    g = tuple(F(level, 2) * weight for level in levels)
                    histogram = probability_histograms(g, schedule, orders)
                    residual = tuple(dot(row, g) for row in matrix)
                    assert residual == tuple(x - y for x, y in zip(histogram, baseline))
                    assert scatter_residual(g, schedule, orders) == residual
                    assert decode_residual(linear_code(g, future), schedule, orders) == residual
                    counts['rro_probability_box_points'] += 1
                    counts['rro_decoder_checks'] += 1
                    if all(level in (0, 2) for level in levels):
                        binary_inputs.append(g)
                        binary_outputs.append(histogram)
                        counts['rro_binary_vertices'] += 1
                labels = canonical(binary_outputs)
                classes = len(set(labels))
                expected_classes = 2 ** dimension if future or not dimension else 2 ** dimension - 1
                assert classes == expected_classes
                assert (classes - 1).bit_length() == dimension
                for i, left in enumerate(binary_inputs):
                    for j, right in enumerate(binary_inputs):
                        difference = tuple(a - b for a, b in zip(left, right))
                        predicted_equal = left == right if future else len(set(difference)) <= 1
                        assert (labels[i] == labels[j]) == predicted_equal
                        counts['rro_binary_pair_kernel_checks'] += 1
                counts['rro_schedule_order_cases'] += 1
    fixtures = endpoint_checks(dot, counts)
    source = Path(__file__).read_bytes()
    result = {
        'theory': 'docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md',
        'section': 46,
        'source': 'docs/reports/contextual-spacetime-ml/rro_retention.py',
        'source_bytes': len(source), 'source_sha256': hashlib.sha256(source).hexdigest(),
        'geometry_source': 'docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md',
        'geometry_assumptions': [
            'RRO 34.0: positive-depth boundary set E1..E_G_L with fixed side orientation',
            'RRO 34.1: tau=0 coordinate product; RRO 34.3: full-cycle constant kernel',
            'Cycle labels are permuted incidence inputs, not derived RRO digit geometry'],
        'scope': 'Fixed finite tuple of marginal histograms; full phase measure retained and charged; exact real residuals. Linear rank is not bits or total memory. Universal claims use paper proofs.',
        'family': {'horizons': [0, 1, 2], 'depths': [0, 1, 2, 3],
                   'max_initial_residual_dimension': max_dimension,
                   'orders': 'natural; permuted M2=(2,1), M3=(3,1,2), M5=(3,1,4,2,5)',
                   'box_grid': 'g_k in {0,1/(2K),1/K}; K=0 has one empty vector',
                   'rank_cases_by_schedule': rank_cases},
        **fixtures}
    return result, counts
