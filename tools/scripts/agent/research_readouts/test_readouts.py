"""Executable contract for issue-backed research readings."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

import readouts

ROOT = Path(__file__).resolve().parent
T0 = '2026-01-01T00:00:00Z'
START = '2026-01-01T01:00:00Z'
END = '2026-01-01T02:00:00Z'
DEADLINE = '2026-01-01T03:00:00Z'
AFTER = '2026-01-01T04:00:00Z'
REPO = 'https://github.com/the-omega-institute/trureturing'
EVENT = {'statement': 'P(n)', 'quantifiers': 'For every natural number n'}


def block(kind, value):
    return '```research-' + kind + '-v1\n' + json.dumps(value) + '\n```'


def carrier(url, body, created=T0):
    return {'html_url': url, 'body': body, 'created_at': created, 'updated_at': created}


def fixture(number=1, p=0.75, answer=True, shape='content', status=None):
    url = f'{REPO}/issues/{number}'
    source = carrier(f'{REPO}/pull/{number + 100}',
                     f'proof_shape: {shape}\nExisting mathematical settlement evidence.', END)
    prereg = {
        'event': EVENT.copy(), 'deadline': DEADLINE,
        'scoring_rule': {'name': 'binary-brier', 'version': 1},
        'surprise_threshold': 0.25,
        'predictions': [{'seat': 'predictor-a', 'model_family': 'family-a',
                         'event': EVENT.copy(), 'probability': p}],
    }
    terminal = {
        'event': EVENT.copy(), 'execution_started_at': START,
        'status': status or ('proved' if answer else 'refuted'),
        'settled_at': END if status not in ('unresolved', 'invalid') else None,
        'evidence': {'url': source['html_url'], 'excerpt': 'Existing mathematical settlement evidence.'},
        'shape_evidence': {'url': source['html_url'], 'excerpt': f'proof_shape: {shape}'}
        if status not in ('unresolved', 'invalid') else None,
    }
    item = {'issue': carrier(url, 'Existing preregistration issue'),
            'comments': [carrier(url + '#issuecomment-2', block('prereg', prereg)),
                         carrier(url + '#issuecomment-1', block('terminal', terminal), END)]}
    return {'issues': [item], 'evidence': [source]}, prereg, terminal


def rebuild(batch, prereg, terminal):
    batch['issues'][0]['comments'][0]['body'] = block('prereg', prereg)
    batch['issues'][0]['comments'][1]['body'] = block('terminal', terminal)
    return batch


def run(batch, as_of=AFTER):
    return readouts.recompute(batch, as_of)


class ReadoutTests(unittest.TestCase):
    def assert_bad(self, batch, code):
        with self.assertRaisesRegex(readouts.ContractError, code):
            run(batch)

    def test_invalid_probabilities_are_named_failures(self):
        for p in (-0.01, 1.01, True, '0.5', None):
            with self.subTest(p=p):
                self.assert_bad(fixture(p=p)[0], 'INVALID_PROBABILITY')

    def test_missing_fields_and_unknown_fields_fail(self):
        for field in ('event', 'deadline', 'scoring_rule',
                      'surprise_threshold', 'predictions'):
            batch, prereg, terminal = fixture()
            del prereg[field]
            self.assert_bad(rebuild(batch, prereg, terminal), 'FIELDS')
        batch, prereg, terminal = fixture()
        prereg['value_function'] = [0] * 5
        self.assert_bad(rebuild(batch, prereg, terminal), 'FIELDS')

    def test_posthoc_prediction_is_rejected(self):
        batch, prereg, terminal = fixture()
        batch['issues'][0]['comments'][0]['created_at'] = END
        batch['issues'][0]['comments'][0]['updated_at'] = END
        self.assert_bad(rebuild(batch, prereg, terminal), 'POSTHOC_PREDICTION')

    def test_carrier_edits_and_payload_backdating_are_rejected(self):
        batch, _, _ = fixture()
        batch['issues'][0]['comments'][0]['updated_at'] = END
        self.assert_bad(batch, 'EDITED_PREREGISTRATION')
        batch, prereg, terminal = fixture()
        prereg['registered_at'] = '2025-12-31T23:59:59Z'
        self.assert_bad(rebuild(batch, prereg, terminal), 'FIELDS')

    def test_event_identity_is_checked_for_forecast_and_terminal(self):
        for target in ('forecast', 'terminal'):
            batch, prereg, terminal = fixture()
            event = prereg['predictions'][0]['event'] if target == 'forecast' else terminal['event']
            event['quantifiers'] = 'For some natural number n'
            self.assert_bad(rebuild(batch, prereg, terminal), 'EVENT_MISMATCH')

    def test_inline_fence_mentions_are_not_registration_blocks(self):
        batch, _, _ = fixture()
        batch['issues'][0]['issue']['body'] = 'Use the inline ` ```research-prereg-v1 ` label.'
        self.assertEqual(run(batch)['units'][0]['mode'], 'p2')

    def test_duplicate_seats_blocks_and_units_are_rejected(self):
        batch, prereg, terminal = fixture()
        prereg['predictions'] *= 2
        self.assert_bad(rebuild(batch, prereg, terminal), 'DUPLICATE_SEAT')
        batch, _, _ = fixture()
        batch['issues'][0]['comments'][0]['body'] += '\n' + batch['issues'][0]['comments'][0]['body']
        self.assert_bad(batch, 'DUPLICATE_BLOCK')
        batch, _, _ = fixture()
        batch['issues'] *= 2
        self.assert_bad(batch, 'DUPLICATE_UNIT')

    def test_rule_version_and_threshold_are_validated(self):
        for field, value, code in [('scoring_rule', {'name': 'binary-brier', 'version': 2}, 'SCORING_RULE'),
                                   ('surprise_threshold', -0.1, 'INVALID_THRESHOLD'),
                                   ('surprise_threshold', 1.1, 'INVALID_THRESHOLD')]:
            batch, prereg, terminal = fixture()
            prereg[field] = value
            self.assert_bad(rebuild(batch, prereg, terminal), code)

    def test_illegal_xz_and_yz_are_rejected(self):
        for xyz in ((1, 0, 1), (0, 1, 1), (1, 1, 1)):
            with self.subTest(xyz=xyz):
                with self.assertRaisesRegex(readouts.ContractError, 'ILLEGAL_MODE'):
                    readouts.classify(*xyz)

    def test_evidence_references_are_resolved_and_excerpts_checked(self):
        batch, _, _ = fixture()
        batch['evidence'] = []
        self.assert_bad(batch, 'DANGLING_EVIDENCE')
        batch, _, _ = fixture()
        batch['evidence'][0]['body'] = 'unrelated proof_shape: bind-only'
        self.assert_bad(batch, 'EVIDENCE_MISMATCH')

    def test_brier_known_example_and_probability_endpoints(self):
        for p, answer, score in ((0.75, True, '1/16'), (0.75, False, '9/16'),
                                  (0, False, '0'), (0, True, '1'),
                                  (1, False, '1'), (1, True, '0')):
            with self.subTest(p=p, answer=answer):
                unit = run(fixture(p=p, answer=answer)[0])['units'][0]
                self.assertEqual(unit['scores'][0]['brier'], score)
                self.assertEqual(unit['score_status'], 'scored')

    def test_aggregate_is_equal_seat_mean_and_y_uses_mean_brier(self):
        batch, prereg, terminal = fixture(p=0)
        prereg['predictions'].append({'seat': 'predictor-b', 'model_family': 'family-b',
                                     'event': EVENT.copy(), 'probability': 1})
        unit = run(rebuild(batch, prereg, terminal))['units'][0]
        self.assertEqual(unit['aggregate_probability'], '1/2')
        self.assertEqual(unit['surprise'], '1/2')
        self.assertEqual(unit['y'], 1)
        self.assertEqual(unit['model_families'], ['family-a', 'family-b'])

    def test_asymmetric_three_seat_arithmetic_means(self):
        batch, prereg, terminal = fixture(p=0)
        prereg['predictions'].extend([
            {'seat': 'predictor-b', 'model_family': 'family-b',
             'event': EVENT.copy(), 'probability': 0},
            {'seat': 'predictor-c', 'model_family': 'family-c',
             'event': EVENT.copy(), 'probability': 1},
        ])
        unit = run(rebuild(batch, prereg, terminal))['units'][0]
        self.assertEqual(unit['aggregate_probability'], '1/3')
        self.assertEqual(unit['surprise'], '2/3')
        self.assertEqual(unit['y'], 1)

    def test_registered_threshold_boundary_is_inclusive(self):
        batch, prereg, terminal = fixture(p=0.5)
        self.assertEqual(run(batch)['units'][0]['y'], 1)
        prereg['surprise_threshold'] = 0.25001
        self.assertEqual(run(rebuild(batch, prereg, terminal))['units'][0]['y'], 0)

    def test_unsettled_is_never_scored_as_a_negative_answer(self):
        result = run(fixture(status='unresolved')[0])
        unit = result['units'][0]
        self.assertEqual((unit['x'], unit['y'], unit['z'], unit['mode']), (0, 0, 1, 'p3'))
        self.assertEqual(unit['scores'], [])
        self.assertIsNone(unit['surprise'])
        self.assertEqual(unit['score_status'], 'unsettled')
        self.assertEqual(result['batch']['score_coverage'], '0')
        self.assertEqual(result['batch']['missing_counts']['answer_units'], 1)

    def test_missing_prediction_never_creates_y_or_a_mode(self):
        batch, prereg, terminal = fixture()
        prereg['predictions'] = []
        result = run(rebuild(batch, prereg, terminal))
        unit = result['units'][0]
        self.assertIsNone(unit['y'])
        self.assertIsNone(unit['mode'])
        self.assertEqual(unit['score_status'], 'missing-predictions')
        self.assertEqual(result['batch']['missing_counts']['prediction_units'], 1)
        self.assertEqual(result['batch']['mode_denominator'], 0)
        self.assertIsNone(result['batch']['X'])

    def test_missing_preregistration_and_missing_shape_remain_unmeasured(self):
        batch, _, _ = fixture()
        batch['issues'][0]['comments'][0]['body'] = 'Historical record without predictions.'
        unit = run(batch)['units'][0]
        self.assertIsNone(unit['y'])
        self.assertIsNone(unit['mode'])
        self.assertEqual(unit['evidence_status'], 'missing-preregistration')
        batch, prereg, terminal = fixture()
        terminal['shape_evidence'] = None
        result = run(rebuild(batch, prereg, terminal))
        self.assertIsNone(result['units'][0]['x'])
        self.assertIsNone(result['units'][0]['mode'])
        self.assertEqual(result['batch']['missing_counts']['shape_units'], 1)

    def test_terminal_contract_is_checked_without_a_scored_answer(self):
        batch, _, _ = fixture()
        batch['issues'][0]['comments'][0]['body'] = 'Historical record without predictions.'
        batch['issues'][0]['comments'][1]['body'] = block('terminal', {})
        self.assert_bad(batch, 'FIELDS')
        batch, prereg, terminal = fixture()
        terminal['settled_at'] = AFTER
        terminal['shape_evidence']['excerpt'] = 'not an existing proof_shape line'
        batch['issues'][0]['comments'][1]['created_at'] = AFTER
        batch['issues'][0]['comments'][1]['updated_at'] = AFTER
        self.assert_bad(rebuild(batch, prereg, terminal), 'EVIDENCE_MISMATCH')

    def test_all_five_modes_and_complete_counts(self):
        batch = {'issues': [], 'evidence': []}
        for n, p, shape, status in ((1, 1, 'bind-only', None), (2, 1, 'content', None),
                                    (3, 0, 'bind-only', None), (4, 0, 'content', None),
                                    (5, 0, 'bind-only', 'unresolved')):
            one, _, _ = fixture(n, p=p, shape=shape, status=status)
            batch['issues'] += one['issues']
            batch['evidence'] += one['evidence']
        result = run(batch)
        self.assertEqual([u['mode'] for u in result['units']], ['p0', 'p2', 'p5', 'p25', 'p3'])
        self.assertEqual(result['batch']['five_counts'], dict.fromkeys(['p0', 'p2', 'p5', 'p25', 'p3'], 1))
        self.assertEqual([result['batch'][k] for k in ('X', 'Y', 'Z')], ['2/5', '2/5', '1/5'])
        self.assertEqual(result['batch']['score_coverage'], '4/5')
        self.assertEqual(result['batch']['mode_coverage'], '1')
        self.assertNotIn('expected_value', result['batch'])
        self.assertNotIn('ranking', result['batch'])

    def test_same_three_rates_different_five_cells_are_distinguished(self):
        def batch_from(cases):
            batch = {'issues': [], 'evidence': []}
            for n, (p, shape) in enumerate(cases, 1):
                one, _, _ = fixture(n, p=p, shape=shape)
                batch['issues'] += one['issues']
                batch['evidence'] += one['evidence']
            return run(batch)['batch']
        a = batch_from([(1, 'content'), (0, 'bind-only')])
        b = batch_from([(1, 'bind-only'), (0, 'content')])
        self.assertEqual([a[k] for k in ('X', 'Y', 'Z')], [b[k] for k in ('X', 'Y', 'Z')])
        self.assertEqual([b['five_counts'][k] - a['five_counts'][k]
                          for k in ('p0', 'p2', 'p5', 'p25', 'p3')], [1, -1, -1, 1, 0])
        self.assertNotEqual(a['five_counts'], b['five_counts'])

    def test_early_settlement_can_be_scored_before_deadline(self):
        unit = run(fixture()[0], END)['units'][0]
        self.assertEqual(unit['mode'], 'p2')
        self.assertEqual(unit['score_status'], 'scored')

    def test_deadline_is_required_for_unresolved_readings(self):
        batch = fixture(status='unresolved')[0]
        with self.assertRaisesRegex(readouts.ContractError, 'BEFORE_DEADLINE'):
            run(batch, END)

    def test_settlement_after_deadline_is_unsettled_at_cutoff(self):
        batch, prereg, terminal = fixture()
        terminal['settled_at'] = AFTER
        batch['issues'][0]['comments'][1]['created_at'] = AFTER
        batch['issues'][0]['comments'][1]['updated_at'] = AFTER
        unit = run(rebuild(batch, prereg, terminal))['units'][0]
        self.assertEqual(unit['mode'], 'p3')
        self.assertEqual(unit['scores'], [])

    def test_future_and_incoherent_times_are_rejected(self):
        batch, prereg, terminal = fixture()
        terminal['settled_at'] = T0
        self.assert_bad(rebuild(batch, prereg, terminal), 'SETTLEMENT_TIME')
        batch, prereg, terminal = fixture()
        batch['issues'][0]['comments'][0]['created_at'] = '2026-01-01'
        self.assert_bad(rebuild(batch, prereg, terminal), 'TIMESTAMP')

    def test_edited_terminal_and_issue_body_registration_are_rejected(self):
        batch, _, _ = fixture()
        batch['issues'][0]['comments'][1]['updated_at'] = AFTER
        self.assert_bad(batch, 'EDITED_TERMINAL')
        batch, _, _ = fixture()
        batch['issues'][0]['issue']['body'] = batch['issues'][0]['comments'].pop(0)['body']
        self.assert_bad(batch, 'PREREG_CARRIER')

    def test_late_terminal_can_report_a_timely_existing_settlement(self):
        batch, _, _ = fixture()
        batch['issues'][0]['comments'][1]['created_at'] = AFTER
        batch['issues'][0]['comments'][1]['updated_at'] = AFTER
        unit = run(batch)['units'][0]
        self.assertEqual(unit['mode'], 'p2')
        self.assertEqual(unit['scores'][0]['brier'], '1/16')

    def test_registration_time_comes_from_unchanged_carrier(self):
        unit = run(fixture()[0])['units'][0]
        self.assertEqual(unit['registered_at'], T0)

    def test_input_order_does_not_change_output(self):
        a = fixture(2)[0]
        b = fixture(1)[0]
        batch = {'issues': a['issues'] + b['issues'], 'evidence': a['evidence'] + b['evidence']}
        reverse = {'issues': list(reversed(batch['issues'])), 'evidence': list(reversed(batch['evidence']))}
        self.assertEqual(run(batch), run(reverse))

    def test_live_loader_names_missing_carrier_fields(self):
        batch, _, _ = fixture()
        issue = batch['issues'][0]['issue'].copy()
        del issue['body']
        with patch.object(readouts, 'gh_json', side_effect=[issue, [[]]]):
            with self.assertRaisesRegex(readouts.ContractError, 'FIELDS'):
                readouts.load_issues([1])

    def test_live_issue_loader_paginates_comments_and_resolves_citations(self):
        batch, _, _ = fixture()
        issue = batch['issues'][0]['issue']
        comments = batch['issues'][0]['comments']
        def api(path, paginate=False):
            if path.endswith('/issues/1'):
                return issue
            if path.endswith('/issues/1/comments'):
                self.assertTrue(paginate)
                return [comments, []]
            if path.endswith('/issues/101'):
                return batch['evidence'][0]
            self.fail(path)
        with patch.object(readouts, 'gh_json', side_effect=api):
            self.assertEqual(run(readouts.load_issues([1])), run(batch))

    def test_cli_strict_json_and_no_partial_stdout_on_failure(self):
        proc = subprocess.run([sys.executable, '-B', str(ROOT / 'readouts.py'), '--as-of', AFTER],
                              input=json.dumps(fixture()[0]), text=True, capture_output=True)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(json.loads(proc.stdout), run(fixture()[0]))
        for bad in ('{"issues": [], "issues": []}', '{"issues": NaN}'):
            proc = subprocess.run([sys.executable, '-B', str(ROOT / 'readouts.py'), '--as-of', AFTER],
                                  input=bad, text=True, capture_output=True)
            self.assertEqual(proc.returncode, 2)
            self.assertEqual(proc.stdout, '')
            self.assertIn('READOUT', proc.stderr)


class NamedResult(unittest.TextTestResult):
    def addFailure(self, test, err):
        super().addFailure(test, err)
        self.stream.writeln('[FAIL] ' + test.id())

    def addError(self, test, err):
        super().addError(test, err)
        self.stream.writeln('[FAIL] ' + test.id())


if __name__ == '__main__':
    unittest.main(testRunner=unittest.TextTestRunner(resultclass=NamedResult, verbosity=2))
