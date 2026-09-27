"""Exact finite witnesses for observation companion §49; not a universal proof.

The sole caller is finite_checks.py. This helper has no RNG, CLI, or writer.
Independent latent likelihood masses check the balance-based next-one readout.
"""
from fractions import Fraction as F
import hashlib
from itertools import combinations, product
from pathlib import Path


def check_static_mixture_horizon() -> tuple[dict, dict[str, int]]:
    if not __debug__:
        raise RuntimeError('static mixture horizon checks require assertions enabled')

    max_word_length, pair_L_max, m_max, threshold_j_max, K_max = 10, 6, 10, 6, 6
    counts = dict.fromkeys((
        'static_mixture_horizon_words',
        'static_mixture_horizon_same_length_pairs',
        'static_mixture_horizon_horizon_fenceposts',
        'static_mixture_horizon_tolerance_fenceposts',
        'static_mixture_horizon_bounded_readout_cases',
        'static_mixture_horizon_clipping_cases'), 0)

    def record(name):
        counts['static_mixture_horizon_' + name] += 1

    def masses(word):
        # Joint masses P(Theta=1/4,w), P(Theta=3/4,w), with no balance input.
        low, high = F(1, 2), F(1, 2)
        for bit in word:
            assert bit in (0, 1)
            low *= F(1, 4) if bit else F(3, 4)
            high *= F(3, 4) if bit else F(1, 4)
        return low, high

    def mass_prediction(word):
        low, high = masses(word)
        assert low > 0 and high > 0, word
        return (low / 4 + 3 * high / 4) / (low + high)

    def prediction(balance):
        # Fraction's negative powers remain exact; integer 3**negative would not.
        odds = F(3) ** balance
        return F(1, 4) + odds / (2 * (1 + odds))

    def c(length):
        assert length >= 0
        return F(3 ** length - 1, 4 * (3 ** length + 1))

    def least_L(epsilon):
        assert 0 < epsilon < F(1, 4)
        length = 1
        # Strict integer comparison, including epsilon=c_j exactly.
        while ((3 ** length - 1) * epsilon.denominator
               <= 4 * epsilon.numerator * (3 ** length + 1)):
            length += 1
        return length

    def bounded_readout(balance, cutoff):
        assert cutoff >= 1
        if balance >= cutoff:
            return F(3, 4)
        if balance <= -cutoff:
            return F(1, 4)
        return prediction(balance)

    words = []
    for length in range(max_word_length + 1):
        balances, outputs, errors = set(), set(), []
        for word in product((0, 1), repeat=length):
            low, high = masses(word)
            balance = 0
            for bit in word:
                balance += 1 if bit else -1
            expected = mass_prediction(word)
            assert low > 0 and high > 0, word
            assert balance == 2 * sum(word) - length, word
            assert high / low == F(3) ** balance, word
            assert high / (low + high) == (F(3) ** balance) / (1 + F(3) ** balance), word
            assert expected == prediction(balance), word
            assert sum(masses(word + (1,))) / (low + high) == expected, word
            assert prediction(-balance) == 1 - expected, word
            balances.add(balance)
            outputs.add(expected)
            errors.append(abs(expected - F(1, 2)))
            words.append((word, expected))
            record('words')
        # Exact count labels, parity, and the best one-state endpoint radius.
        assert balances == set(range(-length, length + 1, 2)), length
        assert len(outputs) == len(balances) == length + 1, length
        assert max(errors) == c(length), length
        record('horizon_fenceposts')

    pair_final_time_max = 0
    empty_suffix_pairs = 0
    for length in range(1, pair_L_max + 1):
        for m in range(1, m_max + 1):
            prefixes = [(1,) * (length * j) + (0,) * (length * (m - j))
                        for j in range(m + 1)]
            for i, j in combinations(range(m + 1), 2):
                suffix_balance = -length * (i + j - m)
                suffix = ((1,) if suffix_balance > 0 else (0,)) * abs(suffix_balance)
                left, right = prefixes[i] + suffix, prefixes[j] + suffix
                distance = length * (j - i)
                assert len(prefixes[i]) == len(prefixes[j]) == length * m, (length, m, i, j)
                assert len(suffix) <= length * (m - 1), (length, m, i, j)
                assert len(left) == len(right) <= (2 * m - 1) * length, (length, m, i, j)
                assert 2 * sum(left) - len(left) == -distance, (length, m, i, j)
                assert 2 * sum(right) - len(right) == distance, (length, m, i, j)
                left_value, right_value = mass_prediction(left), mass_prediction(right)
                assert left_value == prediction(-distance), (length, m, i, j)
                assert right_value == prediction(distance), (length, m, i, j)
                assert (right_value - left_value) / 2 == c(distance) >= c(length), (length, m, i, j)
                pair_final_time_max = max(pair_final_time_max, len(left))
                empty_suffix_pairs += not suffix
                record('same_length_pairs')

        epsilon = (c(length - 1) + c(length)) / 2
        assert least_L(epsilon) == length
        for horizon in range(2 * m_max * length + 1):
            m = (horizon + length) // (2 * length)
            feasible = [0] + [n for n in range(1, m_max + 2)
                              if (2 * n - 1) * length <= horizon]
            assert m == max(feasible), (length, horizon)
            assert 1 + horizon // (2 * length) <= 1 + m <= horizon + 1, (length, horizon)
            if m:
                assert length * m <= (2 * m - 1) * length <= horizon, (length, horizon)
            else:
                assert horizon < length, (length, horizon)
            endpoints = [mass_prediction((bit,) * horizon) for bit in (0, 1)]
            radius = (endpoints[1] - endpoints[0]) / 2
            assert radius == c(horizon), (length, horizon)
            assert (radius <= epsilon) == (horizon < length), (length, horizon)
            record('horizon_fenceposts')
    assert empty_suffix_pairs > 0

    threshold_L_max = 0
    for j in range(1, threshold_j_max + 1):
        for epsilon, expected_L in (((c(j - 1) + c(j)) / 2, j),
                                    (c(j), j + 1),
                                    ((c(j) + c(j + 1)) / 2, j + 1)):
            length = least_L(epsilon)
            assert length == expected_L and c(length - 1) <= epsilon < c(length), (j, epsilon)
            threshold_L_max = max(threshold_L_max, length)
            record('tolerance_fenceposts')
    # These domains do not enter least_L or the positive-epsilon proposition.
    for horizon in range(max_word_length + 1):
        for epsilon in (F(0), F(1, 4), F(1, 3)):
            if epsilon == 0:
                values = {mass_prediction((1,) * n + (0,) * (horizon - n))
                          for n in range(horizon + 1)}
                assert len(values) == horizon + 1, horizon
                assert (c(horizon) <= epsilon) == (horizon == 0), horizon
            else:
                assert c(horizon) < F(1, 4) <= epsilon, (horizon, epsilon)
            record('tolerance_fenceposts')
    assert masses(()) == (F(1, 2), F(1, 2)) and prediction(0) == F(1, 2)

    readout_balance_abs_max = 0
    for cutoff in range(1, K_max + 1):
        tail_error = F(1, 2 * (1 + 3 ** cutoff))

        def check_readout(balance, expected):
            value = bounded_readout(balance, cutoff)
            assert abs(value - expected) <= tail_error, (cutoff, balance)
            if abs(balance) < cutoff:
                assert value == expected, (cutoff, balance)
            else:
                assert abs(value - expected) == F(1, 2 * (1 + 3 ** abs(balance))), (cutoff, balance)
            assert value.denominator <= 4 * (1 + 3 ** (cutoff - 1)), (cutoff, balance)
            assert value.numerator.bit_length() + value.denominator.bit_length() <= 4 * cutoff + 6
            record('bounded_readout_cases')

        for word, expected in words:
            # Updating the full counter never uses or feeds back the saturated output.
            balance = 0
            for bit in word:
                balance += 1 if bit else -1
            check_readout(balance, expected)
        for balance in range(-2 * cutoff - 1, 2 * cutoff + 2):
            word = ((1,) if balance > 0 else (0,)) * abs(balance)
            check_readout(balance, mass_prediction(word))
            readout_balance_abs_max = max(readout_balance_abs_max, abs(balance))

        word = (1,) * (2 * cutoff) + (0,) * (2 * cutoff)
        full, clipped = 0, 0
        for bit in word:
            step = 1 if bit else -1
            full += step
            clipped = min(cutoff, max(-cutoff, clipped + step))
        assert full == 0 and clipped == -cutoff, cutoff
        expected = mass_prediction(word)
        assert expected == F(1, 2) and bounded_readout(clipped, cutoff) == F(1, 4), cutoff
        assert abs(bounded_readout(clipped, cutoff) - expected) == F(1, 4) > tail_error, cutoff
        record('clipping_cases')

    # Full-horizon clipping is safe on every prefix, including horizon zero.
    for horizon in range(max_word_length + 1):
        for word, expected in words:
            if len(word) > horizon:
                continue
            full, clipped = 0, 0
            for bit in word:
                step = 1 if bit else -1
                full += step
                clipped = min(horizon, max(-horizon, clipped + step))
                assert full == clipped, (horizon, word)
            assert prediction(clipped) == expected, (horizon, word)
            record('clipping_cases')

    source = Path(__file__).read_bytes()
    payload = {
        'section': 49,
        'theory': 'docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md',
        'source': 'docs/reports/contextual-spacetime-ml/static_mixture_horizon.py',
        'source_bytes': len(source),
        'source_sha256': hashlib.sha256(source).hexdigest(),
        'family': {'max_word_length': max_word_length, 'pair_L_max': pair_L_max,
                   'm_max': m_max, 'threshold_j_max': threshold_j_max, 'K_max': K_max,
                   'threshold_L_max': threshold_L_max, 'horizon_T_max': 2 * m_max * pair_L_max,
                   'pair_final_time_max': pair_final_time_max, 'empty_suffix_pairs': empty_suffix_pairs,
                   'readout_balance_abs_max': readout_balance_abs_max,
                   'clipping_horizon_max': max_word_length, 'clipping_witness_word_max': 4 * K_max},
        'sharp_bound': '1+floor((T+L)/(2L))',
        'strict_threshold': 'epsilon=c_j gives L=j+1',
        'clipping': {'word': '1^(2K)0^(2K)', 'true_balance': 0, 'clamped_balance': '-K',
                     'predicted': '1/4', 'true_next_one': '1/2', 'error': '1/4'},
        'bounded_readout': 'unclipped integer balance; K>=1; tail error <=1/(2*(1+3^K)); exact inner table',
        'state_accounting': 'all persistent history-bearing state, including control/scratch; public t is exogenous',
        'scope': 'Exact finite checks, not universal proof, observer enumeration, exact positive-epsilon or joint epsilon/T optimum, total-memory/runtime optimum, or Lean verification.'}
    return payload, counts
