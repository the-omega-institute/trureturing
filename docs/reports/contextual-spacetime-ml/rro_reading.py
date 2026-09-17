"""Exact finite temporal-reading checks for ML observation companion section 47.

The sole consumer is finite_checks.py. Integer mechanical words are compared
with greedy natural digits and the literal successor on eventually periodic
states; the finite comparisons supplement, rather than prove, the paper claims.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
from math import isqrt
from pathlib import Path
from typing import Callable


@dataclass(frozen=True)
class _State:
    """An exact infinite word: finite prefix followed by a period of length 1 or 2."""

    prefix: tuple[int, ...]
    period: tuple[int, ...]

    def digit(self, index: int) -> int:
        if index < len(self.prefix):
            return self.prefix[index]
        return self.period[(index - len(self.prefix)) % len(self.period)]

    def first(self, length: int) -> str:
        return ''.join(str(self.digit(j)) for j in range(length))


def _same_state(left: _State, right: _State) -> bool:
    # All periods used here divide 2, so two tail positions decide tail equality.
    length = max(len(left.prefix), len(right.prefix)) + 2
    return left.first(length) == right.first(length)


def _successor(state: _State) -> _State:
    """RRO 20.1: find the first literal 00, or collapse an alternating endpoint."""
    for j in range(len(state.prefix) + len(state.period)):
        if state.digit(j) == state.digit(j + 1) == 0:
            end = max(len(state.prefix), j + 1)
            prefix = tuple(0 if k < j else 1 if k == j else state.digit(k)
                           for k in range(end))
            period = tuple(state.digit(end + k) for k in range(len(state.period)))
            return _State(prefix, period)
    return _State((), (0,))


def _natural(number: int, weights: list[int]) -> _State:
    remainder = number
    digits = [0] * len(weights)
    for j in range(len(weights) - 1, -1, -1):
        if weights[j] <= remainder:
            digits[j] = 1
            remainder -= weights[j]
    assert remainder == 0 and all(a * b == 0 for a, b in zip(digits, digits[1:]))
    assert sum(g * b for g, b in zip(weights, digits)) == number
    while digits and digits[-1] == 0:
        digits.pop()
    return _State(tuple(digits), (0,))


def _floor_beta(k: int) -> int:
    """floor(k * (3-sqrt(5))/2), with no floating phase or endpoint choice."""
    if k < 0:
        return -_floor_beta(-k) - 1
    if k == 0:
        return 0
    return (3 * k - isqrt(5 * k * k) - 1) // 2


def _mechanical(offset: int, upper: bool, length: int) -> str:
    rounding = (lambda k: -_floor_beta(-k)) if upper else _floor_beta
    bits = [rounding(offset + t + 1) - rounding(offset + t) for t in range(length)]
    assert all(bit in (0, 1) for bit in bits)
    return ''.join(map(str, bits))


def _adaptive(depth: int, read: Callable[[int], int], weights: list[int]):
    """The controller receives only the public depth and its actual read callback."""
    prefix, value, records = '', 0, []
    while len(prefix) < depth:
        ell = len(prefix)
        index = weights[ell + 1] - value - 2
        assert not records or index > records[-1][0]
        bit = read(index)
        assert bit in (0, 1)
        records.append((index, bit))
        if bit == ell % 2:
            prefix += '0'
        else:
            prefix += '10'
            value += weights[ell]
    return prefix[:depth], records


def _fill_omitted(length: int, selected: dict[int, str]) -> str:
    """Recover isolated omitted centers from their two actually read neighbors."""
    recovered = []
    for index in range(length):
        if index in selected:
            recovered.append(selected[index])
        else:
            assert index - 1 in selected and index + 1 in selected
            recovered.append('1' if selected[index - 1] == selected[index + 1] == '0' else '0')
    return ''.join(recovered)


def check_rro_reading() -> tuple[dict, dict[str, int]]:
    """Run the complete sealed family; return the result payload and disjoint counts."""
    max_depth, endpoint_max, max_subset_depth = 12, 378, 5
    word_length = endpoint_max + 2
    weights = [1, 2]
    while len(weights) < max_depth + 4:
        weights.append(weights[-1] + weights[-2])
    counts = {f'rro_reading_{name}': 0 for name in (
        'natural_representatives', 'endpoint_states', 'mechanical_successor_checks',
        'block_nodes', 'clock_parity_checks', 'candidate_set_checks', 'decoding_checks',
        'forbidden_word_checks', 'zero_window_checks', 'seam_checks',
        'future_boundary_checks', 'fixed_subsets', 'fixed_decoding_checks',
        'missed_window_witnesses')}

    def record(name, count=1):
        counts['rro_reading_' + name] += count

    naturals = [_natural(n, weights) for n in range(weights[max_depth] + word_length)]
    endpoints = {}
    for m in range(1, endpoint_max + 1):
        if m == 1:
            minus, plus = _State((), (0, 1)), _State((), (1, 0))
        else:
            ell = 0
            while weights[ell + 1] < m:
                ell += 1
            prefix = naturals[weights[ell + 1] - m].first(ell)
            assert not prefix or prefix[-1] == '0'
            zero = _State(tuple(map(int, prefix + '0')), (0, 1))
            ten = _State(tuple(map(int, prefix + '10')), (0, 1))
            minus, plus = (ten, zero) if ell % 2 == 0 else (zero, ten)
        endpoints[m, '-'], endpoints[m, '+'] = minus, plus
        record('endpoint_states', 2)

    def audit_orbit(initial, word, expected):
        state = initial
        for t, bit in enumerate(word):
            assert state.digit(0) == int(bit) and _same_state(state, expected(t))
            record('mechanical_successor_checks')
            if t + 1 < len(word):
                state = _successor(state)
        assert '11' not in word
        assert '000' not in word
        record('forbidden_word_checks', 2)

    natural_words = []
    for n in range(weights[max_depth]):
        word = _mechanical(n + 1, False, word_length)
        audit_orbit(naturals[n], word, lambda t, n=n: naturals[n + t])
        natural_words.append(word)
    endpoint_words = {}
    for (m, side), state in endpoints.items():
        word = _mechanical(1 - m, side == '+', word_length)
        audit_orbit(state, word, lambda t, m=m, side=side:
                    endpoints[m - t, side] if t < m else naturals[t - m])
        endpoint_words[m, side] = word
    for m in range(1, endpoint_max + 1):
        minus, plus = endpoint_words[m, '-'], endpoint_words[m, '+']
        differences = [t for t, (a, b) in enumerate(zip(minus, plus)) if a != b]
        assert differences == ([0] if m == 1 else [m - 2, m - 1])
        if m > 1:
            assert minus[m - 2:m] == '10' and plus[m - 2:m] == '01'
    assert endpoint_words[1, '-'][1:] == endpoint_words[1, '+'][1:] == natural_words[0][:-1]
    assert '1' in natural_words[0]  # Zero initial digits do not give all-zero reports.

    all_records = list(zip(naturals[:weights[max_depth]], natural_words))
    endpoint_records = [(state, endpoint_words[key]) for key, state in endpoints.items()]
    all_records.extend(endpoint_records)

    def audit_block(prefix, history):
        ell = len(prefix)
        if ell >= max_depth:
            return
        value = sum(weights[j] * int(bit) for j, bit in enumerate(prefix))
        index = weights[ell + 1] - value - 2
        record('block_nodes')
        # Only actual ancestor reads enter this compatibility computation.
        compatible = {i for i, (_, word) in enumerate(all_records)
                      if all(int(word[k]) == bit for k, bit in history)}
        cylinder = {i for i, (state, _) in enumerate(all_records)
                    if state.first(ell) == prefix}
        assert compatible == cylinder and cylinder
        assert len({all_records[i][1][:index] for i in cylinder}) == 1
        record('candidate_set_checks')
        for block, bit, increment in (('0', ell % 2, weights[ell]),
                                      ('10', 1 - ell % 2, weights[ell + 1])):
            child = prefix + block
            selected = {i for i in compatible if int(all_records[i][1][index]) == bit}
            expected = {i for i, (state, _) in enumerate(all_records)
                        if state.first(len(child)) == child}
            assert selected == expected and selected
            record('candidate_set_checks')
            child_value = value + (weights[ell] if block == '10' else 0)
            child_index = weights[len(child) + 1] - child_value - 2
            assert child_index - index == increment > 0
            side = '+' if bit == 0 else '-'
            witness = _State(tuple(map(int, child)), (0, 1))
            assert _same_state(witness, endpoints[index + 2, side])
            assert int(endpoint_words[index + 2, side][index]) == bit
            record('clock_parity_checks')
            audit_block(child, history + [(index, bit)])

    audit_block('', [])
    inverse_tables, depth_records, examples, zero_paths = {}, {}, {}, {}
    for depth in range(max_depth + 1):
        size = weights[depth]
        horizon = size - 1
        last = horizon - 1
        table = {natural_words[n][:horizon]: naturals[n].first(depth) for n in range(size)}
        assert len(table) == size
        inverse_tables[depth] = table
        rows = list(zip(naturals[:size], natural_words[:size])) + endpoint_records
        depth_records[depth] = rows
        record('natural_representatives', size)
        selected = list(range(0, horizon, 2))
        if horizon and last not in selected:
            selected.append(last)
        assert len(selected) == (0 if depth == 0 else (size + 1) // 2)
        worst_reads, worst_last = 0, None
        for row_index, (state, word) in enumerate(rows):
            answer, reads = _adaptive(depth, lambda t, word=word: int(word[t]), weights)
            assert answer == state.first(depth) == table[word[:horizon]]
            assert len(reads) <= depth
            if reads:
                assert reads[0][0] == 0 and reads[-1][0] <= last
                worst_last = max(worst_last if worst_last is not None else 0, reads[-1][0])
            else:
                assert depth == 0
            worst_reads = max(worst_reads, len(reads))
            if row_index == 0:
                zero_paths[depth] = [k for k, _ in reads]
            recovered = _fill_omitted(horizon, {k: word[k] for k in selected})
            assert recovered == word[:horizon] and table[recovered] == answer
            record('decoding_checks')
        assert worst_reads == depth and worst_last == (last if depth else None)
        assert zero_paths[depth] == [weights[j + 1] - 2 for j in range(depth)]
        examples[depth] = [worst_reads, len(selected), worst_last]

        for m in range(1, endpoint_max + 1):
            prefix_differs = endpoints[m, '-'].first(depth) != endpoints[m, '+'].first(depth)
            word_differs = endpoint_words[m, '-'][:horizon] != endpoint_words[m, '+'][:horizon]
            assert prefix_differs == word_differs == (depth > 0 and m <= size)
            if depth == 0 or m > size:
                record('future_boundary_checks')
        if depth == 0:
            continue
        # Exact lower-bound witnesses at the seam, deadline, and zero-path windows.
        assert endpoints[1, '-'].first(depth) != endpoints[1, '+'].first(depth)
        assert endpoint_words[1, '-'][1:] == endpoint_words[1, '+'][1:]
        record('seam_checks')
        minus, plus = endpoint_words[size, '-'], endpoint_words[size, '+']
        assert minus[:last] == plus[:last] and minus[last] != plus[last]
        for j in range(1, depth):
            m = weights[j + 1]
            k = m - 2
            minus, plus = endpoint_words[m, '-'], endpoint_words[m, '+']
            assert endpoints[m, '-'].first(depth) != endpoints[m, '+'].first(depth)
            assert minus[:k] == plus[:k] == natural_words[0][:k]
            assert minus[k:k + 2] == '10' and plus[k:k + 2] == '01'
            assert minus[k + 2:] == plus[k + 2:]
            assert any(t in (k, k + 1) for t in zero_paths[depth])
            if j > 1:
                assert weights[j] - 1 < k
            record('zero_window_checks')
        obligations = [{0}] + [{m - 2, m - 1} for m in range(2, size + 1)]
        assert max(set().union(*obligations)) == last + 1
        for k in range(size + 1):
            assert sum(k in window for window in obligations) <= 2
        assert all(size not in window for window in obligations)

    # Enumerate every subset of 0..D_L, including the unique empty-depth subset.
    for depth in range(max_subset_depth + 1):
        size, horizon = weights[depth], weights[depth] - 1
        rows, table = depth_records[depth], inverse_tables[depth]
        minimum = None
        for mask in range(1 << horizon):
            selected = [k for k in range(horizon) if mask & (1 << k)]
            hits = depth == 0 or (0 in selected and all(
                m - 2 in selected or m - 1 in selected for m in range(2, size + 1)))
            seen, collision = {}, False
            for state, word in rows:
                transcript = ''.join(word[k] for k in selected)
                answer = state.first(depth)
                if transcript in seen and seen[transcript] != answer:
                    collision = True
                seen[transcript] = answer
                if hits:
                    recovered = _fill_omitted(horizon, {k: word[k] for k in selected})
                    assert recovered == word[:horizon] and table[recovered] == answer
                    record('fixed_decoding_checks')
            assert hits == (not collision)
            if hits:
                minimum = len(selected) if minimum is None else min(minimum, len(selected))
            record('fixed_subsets')
        assert minimum == (0 if depth == 0 else (size + 1) // 2)

    minus, plus = endpoint_words[6, '-'], endpoint_words[6, '+']
    prefix_pair = sorted(endpoints[6, side].first(5) for side in ('-', '+'))
    indices = zero_paths[5]
    differences = [t for t, (a, b) in enumerate(zip(minus, plus)) if a != b]
    common = ''.join(minus[k] for k in indices)
    assert indices == [0, 1, 3, 6, 11] and differences == [4, 5]
    assert prefix_pair == ['01000', '01010']
    assert common == ''.join(plus[k] for k in indices) == '00000'
    assert examples[5] == [5, 7, 11] and examples[12] == [12, 189, 375]
    record('missed_window_witnesses')
    assert counts['rro_reading_natural_representatives'] == 985
    assert counts['rro_reading_endpoint_states'] == 756
    assert counts['rro_reading_block_nodes'] == weights[max_depth] - 1 == 376
    assert counts['rro_reading_fixed_subsets'] == 4247
    assert all(key.startswith('rro_reading_') and type(value) is int and value >= 0
               for key, value in counts.items())
    source = Path(__file__).read_bytes()
    reading = {
        'section': 47,
        'theory': 'docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md',
        'source': 'docs/reports/contextual-spacetime-ml/rro_reading.py',
        'source_bytes': len(source), 'source_sha256': hashlib.sha256(source).hexdigest(),
        'geometry_source': 'docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md',
        'geometry_assumptions': [
            'RRO 20.1–20.7: arithmetic successor T, initial q_L, both complete split-endpoint conventions.',
            'RRO 35.1: block-cylinder splitting clock and its two actual endpoint witnesses.'],
        'scope': 'Initial prefix on one non-resettable trajectory; deterministic noiseless all-state paper task. Exact finite checks, not a universal proof, latency speedup, total-cost optimum or Lean claim.',
        'family': {'min_depth': 0, 'max_depth': max_depth,
                   'endpoint_index_min': 1, 'endpoint_index_max': endpoint_max,
                   'max_fixed_subset_depth': max_subset_depth,
                   'block_digit_length_upper_exclusive': max_depth},
        'depth_examples': {'L5_adaptive_fixed_last': examples[5],
                           'L12_adaptive_fixed_last': examples[12]},
        'missed_window': {'depth': 5, 'endpoint_index': 6, 'prefix_pair': prefix_pair,
                          'zero_branch_indices': indices, 'differing_indices': differences,
                          'common_selected_record': common}}
    return reading, counts
