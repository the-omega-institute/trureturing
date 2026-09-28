#!/usr/bin/env python3
"""Finite reset-free certificates extending sections 55.1, 84 and 88.

Python >=3.10, standard library; --output PATH is relative to the caller.
Companion imports are relative to this file and do not run prior certificates.
The constructor expands arithmetic into complete finite successor tables. The
interpreter only executes those tables against one dial and one persistent
source. Halt has no enabled transition, including no artificial self-loop.

full_turn retains both complete original invocations (first halt edges are
redirected); known_read specializes the second invocation on zero-distance
branches by omitting its already-known S read. This is experimental finite
verification, not Lean closure or an independent implementation review.
"""

import argparse
from collections import Counter
import importlib.util
from itertools import product
import json
from pathlib import Path
import re
import sys
from typing import NamedTuple

if sys.version_info < (3, 10):
    raise RuntimeError('This certificate requires Python >=3.10.')
if not __debug__:
    raise RuntimeError('Exact verification requires assertions; remove -O/PYTHONOPTIMIZE.')

_spec = importlib.util.spec_from_file_location(
    'two51_reset_free_queries', Path(__file__).resolve().with_name('verify_queries.py'))
if _spec is None or _spec.loader is None:
    raise ImportError('Cannot load companion controller semantics.')
_queries = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_queries)
original_step = _queries.original_step
DIMS = _queries.DIMS
POINTS = tuple(_queries.POINTS)

State = tuple
Source = tuple[int, int, int, int]
QUERY_ORDER = (1, 2, 3, 0)
ANSWERS = {'R': tuple(range(5)), 'W': (None,), 'H': (),
           **{f'Q{i}': tuple(range(n)) for i, n in enumerate(DIMS)}}
ORIGINAL_STATES = (('S', 0),) + tuple(
    (kind, b) for kind in ('F', 'G', 'WF', 'WG1', 'WG2') for b in range(5)
) + tuple(('H', x) for x in range(25))
NONHALTS = tuple(q for q in ORIGINAL_STATES if q[0] != 'H')
START = ('L', 'S', 0)


class Row(NamedTuple):
    action: str
    successors: tuple[State, ...]
    output: tuple[int, ...] | None = None


class Configuration(NamedTuple):
    state: State
    dial: int
    source: Source


class Event(NamedTuple):
    before: Configuration
    action: str
    answer: int | None
    after: Configuration


class Run(NamedTuple):
    events: tuple[Event, ...]
    terminal: Configuration
    output: tuple[int, ...]


def original_action(q):
    return 'H' if q[0] == 'H' else 'W' if q[0].startswith('W') else 'R'


def original_table(literal=False):
    table = {}
    for q in ORIGINAL_STATES:
        action = original_action(q)
        successors = []
        for answer in ANSWERS[action]:
            successor = original_step(q, 0 if answer is None else answer)
            if literal and q[0] == 'F' and (answer - q[1]) % 5 == 4:
                successor = ('H', 0)
            successors.append(successor)
        table[q] = Row(action, tuple(successors), (q[1],) if action == 'H' else None)
    return table


def physical_action(action, dial, source):
    """Only the environment reads/moves the dial or reads the persistent source."""
    if action == 'W':
        return None, (dial + 1) % 25, source
    if action == 'R':
        return dial // 5, dial, source
    if action in ('Q0', 'Q1', 'Q2', 'Q3'):
        return source[int(action[1])], dial, source
    raise ValueError(f'No enabled physical action: {action}')


def execute(table, start, dial, source):
    """No preparation formula or state-name dispatch occurs in the interpreter."""
    config = Configuration(start, dial, source)
    events, seen = [], set()
    while True:
        assert config not in seen, ('Physical cycle', config)
        seen.add(config)
        row = table[config.state]
        if row.action == 'H':
            assert row.successors == () and row.output is not None
            return Run(tuple(events), config, row.output)
        answer, new_dial, new_source = physical_action(row.action, config.dial, config.source)
        successor = row.successors[ANSWERS[row.action].index(answer)]
        after = Configuration(successor, new_dial, new_source)
        events.append(Event(config, row.action, answer, after))
        config = after


def encode(source):
    a, b, c, d = source
    j = 4*b + 2*c + d
    return 5*a + j % 5, j // 5


def decode(x, record):
    j = 5*record + x % 5
    j = j if j < 12 else 0
    return x // 5, j // 4, (j % 4) // 2, j % 2


def localizations(original):
    runs = {s: execute(original, ('S', 0), s, POINTS[0]) for s in range(25)}
    for s, run in runs.items():
        assert run.output == (s,)
        assert run.terminal.dial == (s + sum(e.action == 'W' for e in run.events)) % 25
    return runs


def construct(variant, original, localized, confuse_initial=False):
    """Compile all answer slots, including physically impossible answers.

    Query state ('Q', p, *prefix) stores an endpoint and b/c/d answers only.
    There is no stored a: the a answer directly selects a fixed successor.
    Waiting state ('W', r, n) executes one W, then decrements its table label.
    The optional modes are used solely for the two specified counterexamples.
    """
    assert variant in ('full_turn', 'known_read', 'naive')
    endpoints = {s: s if confuse_initial else run.terminal.dial
                 for s, run in localized.items()}
    table = {}
    for q in NONHALTS:
        row = original[q]
        successors = tuple(('Q', endpoints[t[1]]) if t[0] == 'H' else ('L', *t)
                           for t in row.successors)
        table[('L', *q)] = Row(row.action, successors)
    for p in sorted(set(endpoints.values())):
        for depth, coordinate in enumerate(QUERY_ORDER):
            for prefix in product(*(range(DIMS[i]) for i in QUERY_ORDER[:depth])):
                successors = []
                for answer in ANSWERS[f'Q{coordinate}']:
                    if depth < 3:
                        successor = ('Q', p, *prefix, answer)
                    else:
                        b, c, d = prefix
                        target, record = encode((answer, b, c, d))
                        distance = (target - p) % 25
                        if distance == 0 and variant == 'known_read':
                            successor = ('C', record, 'WG2', answer)
                        elif distance == 0 and variant == 'naive':
                            successor = ('C', record, 'S', 0)
                        else:
                            successor = ('W', record, distance or 25)
                    successors.append(successor)
                table[('Q', p, *prefix)] = Row(f'Q{coordinate}', tuple(successors))
    # Fill only chains required by actual enabled source-answer successors.
    pending = {t for row in table.values() for t in row.successors if t[0] == 'W'}
    while pending:
        q = min(pending)
        pending.remove(q)
        _, record, left = q
        successor = ('W', record, left-1) if left > 1 else ('C', record, 'S', 0)
        table[q] = Row('W', (successor,))
        if successor[0] == 'W' and successor not in table:
            pending.add(successor)
    for record in range(3):
        for q, row in original.items():
            output = decode(q[1], record) if row.action == 'H' else None
            table[('C', record, *q)] = Row(
                row.action, tuple(('C', record, *t) for t in row.successors), output)
    return table


def rotate_original(q):
    kind, label = q
    if kind == 'S':
        return q
    return kind, (label + (5 if kind == 'H' else 1)) % (25 if kind == 'H' else 5)


def rotate_state(q):
    if q[0] == 'L':
        return ('L', *rotate_original(q[1:]))
    if q[0] == 'C':
        return ('C', q[1], *rotate_original(q[2:]))
    if q[0] == 'Q':
        return ('Q', (q[1]+5) % 25, *q[2:])
    assert q[0] == 'W'
    return q


def rotate_source(source):
    a, b, c, d = source
    return (a+1) % 5, b, c, d


def rotate_answer(action, answer):
    return (answer+1) % 5 if action in ('R', 'Q0') else answer


def covariance(table):
    failures, slots, terminal_checks = [], 0, 0
    assert {rotate_state(q) for q in table} == set(table)
    for q, row in sorted(table.items()):
        rotated = q
        for _ in range(5):
            rotated = rotate_state(rotated)
        assert rotated == q
        rotated_row = table[rotate_state(q)]
        assert rotated_row.action == row.action
        if row.action == 'H':
            assert rotated_row.output == rotate_source(row.output)
            terminal_checks += 1
        for answer, successor in zip(ANSWERS[row.action], row.successors):
            slots += 1
            shifted_answer = rotate_answer(row.action, answer)
            actual = rotated_row.successors[ANSWERS[row.action].index(shifted_answer)]
            expected = rotate_state(successor)
            if actual != expected:
                failures.append({'state': q, 'answer': answer,
                                 'rotated_successor': expected, 'actual_successor': actual})
    return {'enabled_slots_checked': slots, 'terminal_outputs_checked': terminal_checks,
            'failures': failures}


def abstract_reachable(table):
    seen, pending = set(), [START]
    while pending:
        q = pending.pop()
        if q not in seen:
            seen.add(q)
            pending.extend(table[q].successors)
    return seen


def validate_table(table, original, localized, variant):
    endpoints = sorted({run.terminal.dial for run in localized.values()})
    expected_queries = {('Q', p, *prefix) for p in endpoints
                        for depth in range(4)
                        for prefix in product(*(range(DIMS[i]) for i in QUERY_ORDER[:depth]))}
    first = {('L', *q) for q in NONHALTS}
    second = {('C', r, *q) for r in range(3) for q in ORIGINAL_STATES}
    chains = {q for q in table if q[0] == 'W'}
    assert set(table) == first | expected_queries | chains | second
    assert len(first) == 26 and len(second) == 153
    assert len(endpoints) == 10 and len(expected_queries) == 220
    for q, row in table.items():
        assert row.action in ANSWERS
        assert len(row.successors) == len(ANSWERS[row.action])
        assert all(t in table for t in row.successors)
        assert (row.output is not None) == (row.action == 'H')
        if q[0] == 'L':
            old = original[q[1:]]
            assert row.action == old.action != 'H'
            assert row.successors == tuple(
                ('Q', localized[t[1]].terminal.dial) if t[0] == 'H' else ('L', *t)
                for t in old.successors)
        elif q[0] == 'C':
            old = original[q[2:]]
            assert row.action == old.action
            assert row.successors == tuple(('C', q[1], *t) for t in old.successors)
            if row.action == 'H':
                assert row.output == decode(q[3], q[1])
        elif q[0] == 'Q':
            prefix = q[2:]
            coordinate = QUERY_ORDER[len(prefix)]
            assert row.action == f'Q{coordinate}'
            for answer, successor in zip(ANSWERS[row.action], row.successors):
                if len(prefix) < 3:
                    assert successor == (*q, answer)
                else:
                    target, record = encode((answer, *prefix))
                    delta = (target - q[1]) % 25
                    if variant == 'known_read' and delta == 0:
                        assert successor == ('C', record, 'WG2', answer)
                    else:
                        assert successor == ('W', record, delta or 25)
        else:
            _, record, left = q
            assert record in range(3) and left in range(1, 26)
            assert row == Row('W', (('W', record, left-1) if left > 1
                                    else ('C', record, 'S', 0),))
    # Required chain lengths are inferred from enabled entries, not predictions.
    entries = {r: sorted({t[2] for q in expected_queries for t in table[q].successors
                          if t[0] == 'W' and t[1] == r}) for r in range(3)}
    for r in range(3):
        assert {q[2] for q in chains if q[1] == r} == set(range(1, max(entries[r])+1))
    reachable = abstract_reachable(table)
    assert reachable == set(table)
    cov = covariance(table)
    assert cov['failures'] == []
    return {'nominal_states': len(table), 'abstract_reachable_states': len(reachable),
            'states_by_action': dict(sorted(Counter(row.action for row in table.values()).items())),
            'states_by_component': dict(sorted(Counter(q[0] for q in table).items())),
            'query_nodes_by_depth_per_endpoint': [
                sum(q[1] == endpoints[0] and len(q) == depth+2 for q in expected_queries)
                for depth in range(4)],
            'waiting_chain_lengths_by_record': [sum(q[1] == r for q in chains) for r in range(3)],
            'waiting_chain_entries_by_record': entries,
            'enabled_transition_slots': sum(len(row.successors) for row in table.values()),
            'halt_enabled_transition_slots': sum(len(row.successors) for row in table.values()
                                                 if row.action == 'H'),
            'artificial_halt_self_loops': 0, 'epsilon_transitions': 0,
            # These are mathematical counterexample slots, not anomaly-ledger
            # records. Keep their explicit list after asserting it is empty.
            'full_table_C5': {'enabled_slots_checked': cov['enabled_slots_checked'],
                              'terminal_outputs_checked': cov['terminal_outputs_checked'],
                              'noncommuting_slots': cov['failures']}}


def dial_word(run):
    return ''.join(e.action for e in run.events if e.action in ('R', 'W'))


def costs(run):
    counts = Counter(e.action for e in run.events)
    return {'dial_reads': counts['R'], 'unit_waits': counts['W'],
            'source_queries': sum(counts[f'Q{i}'] for i in range(4)),
            'resets': 0, 'total_actions': len(run.events)}


def witness(initial, source, run, localized):
    first = [e for e in run.events if e.before.state[0] == 'L']
    waiting = [e for e in run.events if e.before.state[0] == 'W']
    second = [e for e in run.events if e.before.state[0] == 'C']
    target, record = encode(source)
    return {'initial_dial': initial, 'source': source,
            'localization_endpoint': localized[initial].terminal.dial,
            'target': target, 'record': record,
            'handoff_state': second[0].before.state, 'handoff_dial': second[0].before.dial,
            'phase_reads': [sum(e.action == 'R' for e in first),
                            sum(e.action == 'R' for e in second)],
            'phase_waits': [sum(e.action == 'W' for e in first), len(waiting),
                            sum(e.action == 'W' for e in second)],
            'terminal_state': run.terminal.state, 'final_dial': run.terminal.dial,
            'decoded_source': run.output, 'costs': costs(run), 'dial_word': dial_word(run)}


def verify_runs(table, variant, localized):
    runs = {(s, source): execute(table, START, s, source)
            for s in range(25) for source in POINTS}
    physical, terminal_pairs, used_sources = set(), set(), set()
    checked = Counter()
    for (s, source), run in runs.items():
        target, record = encode(source)
        endpoint = localized[s].terminal.dial
        delta = (target - endpoint) % 25
        specialized = variant == 'known_read' and delta == 0
        checked['zero_distance_handoffs'] += delta == 0
        checked['specialized_second_invocations'] += specialized
        checked['intact_second_invocations'] += not specialized
        waits = 0
        for event in run.events:
            q, pos, persistent = event.before
            physical.add(q)
            assert persistent == event.after.source == source
            assert pos == (s + waits) % 25
            if event.action == 'W':
                waits += 1
                assert event.answer is None and event.after.dial == (pos+1) % 25
            else:
                assert event.after.dial == pos
                if event.action == 'R':
                    assert event.answer == pos // 5
                else:
                    assert event.answer == source[int(event.action[1])]
            checked['physical_action_invariants'] += 1
            if q[0] == 'Q':
                assert q[1] == pos == endpoint
                assert q[2:] == tuple(source[i] for i in QUERY_ORDER[:len(q)-2])
                checked['source_query_position_checks'] += 1
        assert run.terminal.source == source and run.terminal.dial == (s+waits) % 25
        physical.add(run.terminal.state)
        assert run.events[-1].action == 'R'
        assert re.fullmatch(r'R(W+R)*', dial_word(run))
        assert [e.action for e in run.events if e.action.startswith('Q')] == ['Q1', 'Q2', 'Q3', 'Q0']
        assert costs(run)['source_queries'] == 4
        first = [e for e in run.events if e.before.state[0] == 'L']
        assert len(first) == len(localized[s].events)
        for actual, old in zip(first, localized[s].events):
            assert actual.before.state == ('L', *old.before.state)
            assert (actual.before.dial, actual.action, actual.answer, actual.after.dial) == (
                old.before.dial, old.action, old.answer, old.after.dial)
        assert first[-1].after.state == ('Q', endpoint)
        assert first[-1].after.dial == endpoint
        checked['localization_exit_checks'] += 1
        second = [e for e in run.events if e.before.state[0] == 'C']
        assert second[0].before.dial == target
        entry = ('WG2', source[0]) if specialized else ('S', 0)
        assert second[0].before.state == ('C', record, *entry)
        if specialized:
            assert second[0].before.dial // 5 == source[0]
        handoff_waits = sum(e.before.state[0] == 'W' for e in run.events)
        assert handoff_waits == (25 if variant == 'full_turn' and delta == 0 else delta)
        checked['handoff_position_checks'] += 1
        expected_second = localized[target].events[int(specialized):]
        assert len(second) == len(expected_second)
        for actual, old in zip(second, expected_second):
            assert actual.before.state == ('C', record, *old.before.state)
            assert actual.after.state == ('C', record, *old.after.state)
            assert (actual.before.dial, actual.action, actual.answer, actual.after.dial) == (
                old.before.dial, old.action, old.answer, old.after.dial)
        assert run.terminal.state == ('C', record, 'H', target)
        assert run.output == source
        terminal_pairs.add((target, record))
        used_sources.add(run.output)
        checked['correct_recoveries'] += 1
        checked['legal_dial_words_ending_in_R'] += 1

    for (s, source), run in runs.items():
        shifted = runs[((s+5) % 25, rotate_source(source))]
        assert len(run.events) == len(shifted.events)
        for actual, rotated in zip(run.events, shifted.events):
            for before, after in ((actual.before, rotated.before), (actual.after, rotated.after)):
                assert after == Configuration(rotate_state(before.state), (before.dial+5) % 25,
                                              rotate_source(before.source))
            assert rotated.action == actual.action
            assert rotated.answer == rotate_answer(actual.action, actual.answer)
            checked['C5_trace_event_checks'] += 1
        assert shifted.output == rotate_source(run.output)
        assert costs(shifted) == costs(run)
        assert dial_word(shifted) == dial_word(run)
        checked['C5_trace_and_cost_checks'] += 1

    assert len(runs) == 1500 and used_sources == set(POINTS)
    assert terminal_pairs == {encode(source) for source in POINTS}
    missing = set(table) - physical
    assert missing == {('C', 2, 'H', 5*a+u) for a in range(5) for u in (2, 3, 4)}
    maxima = {name: max(costs(run)[name] for run in runs.values())
              for name in costs(next(iter(runs.values())))}
    witnesses = {name: witness(s, source, run, localized)
                 for name, maximum in maxima.items()
                 for s, source, run in [next((s, source, run) for (s, source), run in runs.items()
                                             if costs(run)[name] == maximum)]}
    histogram = Counter((costs(run)['dial_reads'], costs(run)['unit_waits']) for run in runs.values())
    return runs, {'physical_initial_dial_source_pairs': len(runs),
                  'physically_reachable_states': len(physical),
                  'physical_states_by_component': dict(sorted(Counter(q[0] for q in physical).items())),
                  'physically_unreachable_states': sorted(missing),
                  'used_terminal_pairs': len(terminal_pairs), 'recovered_source_points': len(used_sources),
                  'used_halt_labels': len({x for x, _ in terminal_pairs}),
                  'used_record_values': len({r for _, r in terminal_pairs}),
                  'checks': dict(sorted(checked.items())), 'maximum_costs': maxima,
                  'maximum_cost_witnesses': witnesses,
                  'cost_histogram': [{'dial_reads': r, 'unit_waits': w, 'cases': n}
                                     for (r, w), n in sorted(histogram.items())]}


def verify_decoder(table):
    rows, outputs, used, invalid = [], set(), set(), set()
    for x, record in product(range(25), range(3)):
        source = table[('C', record, 'H', x)].output
        a, b, c, d = source
        j = 4*b + 2*c + d
        raw_j = 5*record + x % 5
        assert source in POINTS and a == x // 5
        assert j == (raw_j if raw_j < 12 else 0)
        assert table[('C', record, 'H', (x+5) % 25)].output == rotate_source(source)
        if raw_j < 12:
            assert encode(source) == (x, record)
            used.add((x, record))
        else:
            invalid.add((x, record))
        outputs.add(source)
        rows.append({'halt_label': x, 'record': record, 'raw_j': raw_j,
                     'valid_encoding': raw_j < 12, 'decoded_a_j': [a, j], 'source': source})
    assert outputs == set(POINTS) and len(used) == 60 and len(invalid) == 15
    return {'terminal_labels_checked': len(rows), 'decoder_range_cardinality': len(outputs),
            'valid_encoding_pairs': len(used), 'invalid_pairs_completed_to_a_j0': len(invalid),
            'labels': rows}


def negative_checks(original, localized, good_runs):
    naive = construct('naive', original, localized)
    naive_runs = {(s, source): execute(naive, START, s, source)
                  for s in range(25) for source in POINTS}
    bad = [(s, source, run) for (s, source), run in naive_runs.items()
           if re.fullmatch(r'R(W+R)*', dial_word(run)) is None]
    assert len(bad) == 65
    assert all(run.output == source for (_, source), run in naive_runs.items())
    assert {(s, source) for s, source, _ in bad} == {
        (s, source) for s in range(25) for source in POINTS
        if encode(source)[0] == localized[s].terminal.dial}
    assert all(dial_word(run).count('RR') == 1 for _, _, run in bad)

    wrong = construct('full_turn', original, localized, confuse_initial=True)
    source = (0, 0, 0, 0)
    wrong_run = execute(wrong, START, 0, source)
    wrong_witness = witness(0, source, wrong_run, localized)
    assert localized[0].terminal.dial == 4
    assert wrong_witness['handoff_dial'] == 4 != encode(source)[0]
    assert wrong_run.output == (0, 1, 0, 0) != source

    literal_original = original_table(literal=True)
    literal_results = {}
    for variant, symmetric_runs in good_runs.items():
        literal = construct(variant, literal_original, localized)
        cov = covariance(literal)
        assert len(cov['failures']) == 20
        unchanged = 0
        for (s, source), expected in symmetric_runs.items():
            assert execute(literal, START, s, source) == expected
            unchanged += 1
        failures_by_component = dict(sorted(Counter(f['state'][0] for f in cov['failures']).items()))
        assert failures_by_component == {'C': 15, 'L': 5}
        literal_results[variant] = {'identical_physical_executions': unchanged,
                                    'full_table_covariance_failures': len(cov['failures']),
                                    'failures_by_component': failures_by_component,
                                    'failed_slots': cov['failures']}
    return {'naive_zero_distance_to_S': {'cases': len(naive_runs), 'spacing_failures': len(bad),
                                        'recovery_failures': 0,
                                        'witness': witness(*bad[0], localized)},
            'initial_position_used_as_current': wrong_witness,
            'literal_section60_unused_F_offset4_to_H0': literal_results}


def verify_action_contract():
    checked = 0
    for action in ANSWERS:
        for dial, source in product(range(25), POINTS):
            if action == 'H':
                try:
                    physical_action(action, dial, source)
                except ValueError:
                    pass
                else:
                    raise AssertionError('Halt enabled a physical action.')
            else:
                answer, after, persistent = physical_action(action, dial, source)
                assert persistent == source
                assert after == ((dial+1) % 25 if action == 'W' else dial)
                assert answer == (None if action == 'W' else dial // 5 if action == 'R'
                                  else source[int(action[1])])
            checked += 1
    return checked


def serialized_table(table):
    # Successors are indexed by the action's declared answer alphabet. A W row
    # has one successor for null; an H row has an empty successor list.
    return [{'state': q, 'action': row.action, 'successors': row.successors,
             **({'output': row.output} if row.output is not None else {})}
            for q, row in sorted(table.items())]


def certificate():
    original = original_table()
    localized = localizations(original)
    variants, runs = {}, {}
    for variant in ('full_turn', 'known_read'):
        table = construct(variant, original, localized)
        summary = validate_table(table, original, localized, variant)
        runs[variant], execution_summary = verify_runs(table, variant, localized)
        summary.update(execution_summary)
        summary['second_invocation_contract'] = (
            'Intact original controller from S on every branch.' if variant == 'full_turn'
            else 'Specialization: zero-distance branches enter WG2_a and omit the known S read; '
                 'positive-distance branches retain the intact invocation.')
        summary['terminal_decoder'] = verify_decoder(table)
        summary['table'] = serialized_table(table)
        variants[variant] = summary
    # These are regression predictions, checked only after constructing tables
    # and independently interpreting enabled transitions on all physical inputs.
    for variant, predicted in [('full_turn', (474, 459, 8, 37)),
                               ('known_read', (469, 454, 8, 36))]:
        result = variants[variant]
        assert (result['nominal_states'], result['physically_reachable_states'],
                result['maximum_costs']['dial_reads'], result['maximum_costs']['unit_waits']) == predicted
        assert result['checks']['zero_distance_handoffs'] == 65
    return {'schema': 'two51-reset-free-finite-tables-v1', 'arithmetic': 'exact integers',
            'action_answer_alphabets': ANSWERS, 'initial_control_state': START,
            'state_labels': {'L': '[L, original kind, original label]',
                             'Q': '[Q, endpoint, previously queried b/c/d prefix]',
                             'W': '[W, record, remaining unit waits]',
                             'C': '[C, record, original kind, original label]'},
            'physical_action_contract_cases': verify_action_contract(),
            'localization': [{'initial': s, 'reads': sum(e.action == 'R' for e in run.events),
                              'waits': sum(e.action == 'W' for e in run.events),
                              'endpoint': run.terminal.dial} for s, run in localized.items()],
            'localization_endpoint_positions': sorted({run.terminal.dial for run in localized.values()}),
            'variants': variants, 'negative_checks': negative_checks(original, localized, runs),
            'scope': 'Exhaustive finite program checks under persistent same-source coordinate queries '
                     'and enlarged finite control. No reset, reverse step, epsilon step, or free halt '
                     'execution is used. Nominal states exclude the 25-position physical dial and '
                     'the 60-point persistent source. Query, dial-read and wait costs are separate. '
                     'No original-archive source-query permission, Lean closure, independent review, '
                     'global time/state optimality, or bidirectional same-budget equivalence is claimed.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    data = json.dumps(certificate(), indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(data, encoding='utf-8')
    else:
        print(data, end='')


if __name__ == '__main__':
    main()
