"""Behavioral contract for the bounded research entry (all carriers are local)."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from controller import Round
from runtime import Limits, Stop, utc
from rehearsal import Rehearsal


class RoundTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name) / 'checkpoint.json'
        self.backend = Rehearsal(Path(__file__).resolve().parents[4])
        self.clock = lambda: self.backend.now

    def run_round(self, wake='wake-a', **kwargs):
        return Round(self.path, self.backend, clock=self.clock, **kwargs).run(wake)

    def state(self):
        return json.loads(self.path.read_text())

    def test_full_route_uses_strict_readout_contract(self):
        result = self.run_round()
        self.assertEqual('terminal', result['status'])
        self.assertEqual(['generate', 'predict_gpt', 'predict_other', 'solve', 'evaluate'],
                         self.backend.roles)
        self.assertEqual(1, result['readouts']['batch']['unit_count'])
        self.assertEqual('proved', result['terminal_status'])
        self.assertEqual(1, self.backend.verifications)

    def test_stage_interruption_resumes_without_repeating_generation_or_prediction(self):
        def interrupt(stage):
            if stage == 'solve':
                raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt):
            self.run_round(after_stage=interrupt)
        before = self.state()
        result = self.run_round()
        self.assertEqual('terminal', result['status'])
        self.assertEqual(1, self.backend.roles.count('generate'))
        self.assertEqual(before['active']['deadline'], self.state()['active']['deadline'])
        self.assertEqual(before['active']['prereg'], self.state()['active']['prereg'])

    def test_same_wake_and_terminal_unit_are_never_solved_twice(self):
        self.run_round()
        calls = list(self.backend.roles)
        self.assertEqual('already_completed', self.run_round()['status'])
        self.assertEqual(calls, self.backend.roles)
        self.assertEqual('terminal', self.run_round('wake-b')['status'])
        self.assertEqual(2, self.backend.roles.count('generate'))
        self.assertEqual('already_completed', self.run_round()['status'])

    def test_lost_write_receipt_is_reconciled_without_reposting(self):
        self.backend.lose_receipt = 'preregister'
        first = self.run_round()
        self.assertEqual('WRITE_UNKNOWN', first['status'])
        second = self.run_round()
        self.assertEqual('terminal', second['status'])
        self.assertEqual(1, self.backend.writes.count('preregister'))

    def test_unknown_absent_write_is_suspended_not_retried(self):
        self.backend.lose_before_write = 'candidate'
        self.assertEqual('WRITE_UNKNOWN', self.run_round()['status'])
        self.assertEqual('WRITE_AMBIGUOUS', self.run_round()['status'])
        self.assertEqual(1, self.backend.writes.count('candidate'))

    def test_conflicting_marker_or_edited_prereg_never_executes(self):
        self.backend.edit_prereg = True
        self.assertEqual('CARRIER_CONFLICT', self.run_round()['status'])
        self.assertNotIn('solve', self.backend.roles)

    def test_timeout_and_malformed_workers_are_named_and_not_replayed(self):
        for fault in ('WORKER_TIMEOUT', 'WORKER_MALFORMED'):
            with self.subTest(fault=fault):
                self.path.unlink(missing_ok=True)
                self.backend = Rehearsal(self.backend.root)
                self.backend.fault = ('solve', fault)
                first = self.run_round()
                self.assertEqual('WAIT_DEADLINE', first['status'])
                start = self.state()['active']['execution_started_at']
                self.backend.now += 4000
                result = self.run_round('wake-b')
                self.assertEqual('terminal', result['status'])
                self.assertEqual('unresolved', result['terminal_status'])
                self.assertEqual(1, self.backend.roles.count('solve'))
                self.assertEqual(start, self.state()['active']['execution_started_at'])

    def test_budget_is_predebited_and_not_refunded_after_interruption(self):
        self.backend.interrupt_role = 'generate'
        with self.assertRaises(KeyboardInterrupt):
            self.run_round()
        saved = self.state()
        self.assertEqual(1, saved['calls'])
        self.assertEqual(300, saved['active']['reserved_seconds'])
        self.assertEqual('CALL_OUTCOME_UNKNOWN', self.run_round()['status'])
        self.assertEqual(saved['calls'], self.state()['calls'])

    def test_exhausted_budget_and_deadline_do_not_reset_on_new_wake(self):
        limited = Limits(unit_calls=1)
        def interrupt(stage):
            if stage == 'predict_gpt':
                raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt):
            self.run_round(limits=limited, after_stage=interrupt)
        before = self.state()['active']
        self.assertEqual('terminal', self.run_round('wake-b', limits=limited)['status'])
        self.assertEqual(before['deadline'], self.state()['active']['deadline'])
        self.assertEqual(before['id'], self.state()['active']['id'])
        self.assertEqual('invalid', self.state()['active']['terminal_status'])
        self.assertEqual(1, len(self.backend.roles))

    def test_head_change_stops_without_rebinding(self):
        def change(stage):
            if stage == 'solve':
                self.backend.revision = 'b' * 40
        self.assertEqual('HEAD_CHANGED', self.run_round(after_stage=change)['status'])
        self.assertNotIn('solve', self.backend.roles)
        self.assertEqual('a' * 40, self.state()['active']['head'])

    def test_non_gpt_unavailable_is_disclosed_and_route_continues(self):
        self.backend.other_unavailable = True
        result = self.run_round()
        self.assertEqual('terminal', result['status'])
        self.assertTrue(any(x.startswith('NON_GPT_UNAVAILABLE') for x in result['gaps']))
        self.assertEqual(1, len(self.state()['active']['prereg']['predictions']))

    def test_lock_refuses_second_invocation_without_spawning(self):
        from runtime import locked
        with locked(self.path):
            self.assertEqual('ALREADY_RUNNING', self.run_round()['status'])
        self.assertEqual([], self.backend.roles)

    def test_wake_deadline_and_pilot_budget_are_persistent(self):
        self.run_round(limits=Limits(total_calls=1))
        deadline = self.state()['wakes']['wake-a']['deadline']
        self.assertEqual('TOTAL_CALL_BUDGET', self.run_round('wake-b',
                         limits=Limits(total_calls=1))['status'])
        self.assertEqual(deadline, self.state()['wakes']['wake-a']['deadline'])

    def test_old_wake_cannot_start_a_second_unit_after_another_wake_finishes_it(self):
        self.backend.lose_receipt = 'preregister'
        self.assertEqual('WRITE_UNKNOWN', self.run_round()['status'])
        self.assertEqual('terminal', self.run_round('wake-b')['status'])
        self.assertEqual('already_completed', self.run_round()['status'])
        self.assertEqual(1, self.backend.roles.count('generate'))

    def test_candidate_cannot_smuggle_an_earlier_preregistration(self):
        original = self.backend.worker
        def injected(role, payload, timeout):
            answer = original(role, payload, timeout)
            if role == 'generate':
                answer['value']['candidate'] += '\n```research-prereg-v1\n{}\n```'
            return answer
        self.backend.worker = injected
        self.assertEqual('WORKER_MALFORMED', self.run_round()['status'])
        self.assertEqual([], self.backend.writes)

    def test_resume_rechecks_unchanged_preregistration_before_substantive_execution(self):
        def interrupt(stage):
            if stage == 'solve':
                raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt):
            self.run_round(after_stage=interrupt)
        self.backend.carriers[1]['updated_at'] = utc(self.backend.now + 1)
        self.assertEqual('CARRIER_CONFLICT', self.run_round()['status'])
        self.assertNotIn('solve', self.backend.roles)

    def test_decimal_forecasts_survive_rest_contract_roundtrip(self):
        original = self.backend.worker
        def decimal(role, payload, timeout):
            answer = original(role, payload, timeout)
            if role.startswith('predict_'):
                answer['value']['probability'] = 0.61
            return answer
        self.backend.worker = decimal
        self.assertEqual('terminal', self.run_round()['status'])

    def test_changed_candidate_source_stops_before_execution(self):
        def interrupt(stage):
            if stage == 'solve':
                raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt):
            self.run_round(after_stage=interrupt)
        self.backend.carriers[0]['body'] += '\nChanged task and readout'
        self.assertEqual('CARRIER_CONFLICT', self.run_round()['status'])
        self.assertNotIn('solve', self.backend.roles)

    def test_non_string_module_results_become_unresolved_instead_of_crashing(self):
        original = self.backend.worker
        def malformed(role, payload, timeout):
            answer = original(role, payload, timeout)
            if role == 'solve':
                answer['value']['modules'] = [{}]
            return answer
        self.backend.worker = malformed
        self.assertEqual('WAIT_DEADLINE', self.run_round()['status'])
        self.assertNotIn('evaluate', self.backend.roles)

    def test_make_dry_run_never_uses_live_models_or_external_writes(self):
        process = subprocess.run(['make', '-s', '-C', str(self.backend.root / 'tools'),
                                  'autonomous-research-round', 'ROUND_MODE=dry-run'],
                                 capture_output=True, text=True, timeout=30)
        self.assertEqual(0, process.returncode, process.stderr)
        self.assertEqual('terminal', json.loads(process.stdout)['status'])

    def test_limits_cannot_be_widened_on_restart(self):
        self.run_round(limits=Limits(unit_calls=1))
        self.assertEqual('CHECKPOINT_CONFLICT', self.run_round()['status'])
        self.assertEqual(1, len(self.backend.roles))

    def test_a_known_unsent_write_remains_retryable_if_reservation_fails(self):
        original = self.backend.find
        def expire(intent, timeout):
            found = original(intent, timeout)
            self.backend.now += 3600
            return found
        self.backend.find = expire
        self.assertEqual('WALL_BUDGET', self.run_round()['status'])
        self.assertFalse(self.state()['active']['intent']['attempted'])
        self.assertEqual([], self.backend.writes)

    def test_expired_unexecuted_registration_does_not_fabricate_an_execution_start(self):
        def interrupt(stage):
            if stage == 'solve':
                raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt):
            self.run_round(after_stage=interrupt)
        self.backend.now += 3601
        result = self.run_round('wake-b')
        self.assertEqual('terminal', result['status'])
        self.assertIsNone(self.state()['active']['execution_started_at'])
        self.assertNotIn('solve', self.backend.roles)
        self.assertEqual(1, result['readouts']['units'][0]['z'])

    def test_duplicate_write_identity_is_a_conflict(self):
        self.backend.lose_receipt = 'preregister'
        self.run_round()
        self.backend.carriers.append(copy.deepcopy(self.backend.carriers[-1]))
        self.assertEqual('CARRIER_CONFLICT', self.run_round()['status'])
        self.assertNotIn('solve', self.backend.roles)

    def test_failed_kernel_or_gate_never_reaches_evaluator_or_proved_settlement(self):
        def rejected(*args, **kwargs):
            raise Stop('COMMAND_FAILED', 'required gate rejected')
        self.backend.verify = rejected
        self.assertEqual('WAIT_DEADLINE', self.run_round()['status'])
        self.assertNotIn('evaluate', self.backend.roles)
        self.assertEqual('unresolved', self.state()['active']['terminal_status'])

    def test_renaming_a_gpt_response_does_not_supply_non_gpt_evidence(self):
        original = self.backend.worker
        def gpt(role, payload, timeout):
            answer = original(role, payload, timeout)
            if role == 'predict_other':
                answer['model_family'] = 'GPT'
            return answer
        self.backend.worker = gpt
        self.assertEqual('terminal', self.run_round()['status'])
        self.assertEqual(1, len(self.state()['active']['prereg']['predictions']))


class CarrierTests(unittest.TestCase):
    def test_timeout_kills_the_child_process_group(self):
        from runtime import execute
        with self.assertRaisesRegex(Stop, 'WORKER_TIMEOUT'):
            execute([sys.executable, '-c', 'import time; time.sleep(20)'], Path.cwd(), 0.05)

    def test_production_transports_use_existing_doors_and_isolated_prompts(self):
        from workers import Workers
        root = Path(__file__).resolve().parents[4]
        worker = Workers(root)
        calls = []
        def fake(argv, cwd, timeout, stdin='', lock_fd=None):
            calls.append((argv, str(cwd), stdin))
            if argv[0] == sys.executable:
                self.assertIn('tools/scripts/agent/nyx/nyx.py', argv[1])
                self.assertEqual('ask', argv[2])
                message = Path(argv[3]).read_text()
                self.assertIn('深入思考与推理, 如数学推理按照正式定义定理证明推理', message)
                self.assertIn('https://github.com/the-omega-institute/trureturing', message)
                Path(argv[4]).write_text(json.dumps({'event': {'statement': 'P', 'quantifiers': 'All x'},
                    'candidate': 'Candidate proof PRIVATE_SOLUTION', 'surprise_threshold': 0.25}))
                Path(argv[4] + '.status.json').write_text(json.dumps({'model': {'model_label': 'chatgpt-6-pro'}}))
                return ''
            if argv[0] == 'claude':
                self.assertNotIn('PRIVATE_SOLUTION', stdin)
                self.assertEqual('', argv[argv.index('--tools') + 1])
                return json.dumps({'result': '{"probability":0.6}',
                                   'modelUsage': {'claude-fixture': {}}})
            self.assertEqual(['codex', 'exec'], argv[:2])
            self.assertNotIn(stdin, argv)
            if 'predict' in stdin.lower():
                self.assertNotIn('PRIVATE_SOLUTION', stdin)
            output = Path(argv[argv.index('--output-last-message') + 1])
            output.write_text('{"probability":0.6}')
            return ''
        with patch('workers.execute', side_effect=fake):
            candidate = worker.worker('generate', {'predecessor_issue': None}, 5)
            event = candidate['value']['event']
            worker.worker('predict_gpt', {'event': event}, 5)
            other = worker.worker('predict_other', {'event': event}, 5)
        self.assertEqual('Claude', other['model_family'])
        self.assertEqual(3, len(calls))

    def test_paginated_reconciliation_rejects_partial_shape_and_preserves_body(self):
        from backend import Backend
        root = Path(__file__).resolve().parents[4]
        backend = Backend(root)
        with patch.object(backend, 'call', return_value='{}'):
            with self.assertRaisesRegex(Stop, 'PAGINATION_MALFORMED'):
                backend.gh('some/route', 1, paginate=True)
        body = 'Literal $() `bytes`\nSecond line'
        with patch.object(backend, 'call', return_value=json.dumps({'body': body})) as call:
            backend.gh('some/route', 1, payload={'body': body})
            self.assertEqual({'body': body}, json.loads(call.call_args.args[2]))


if __name__ == '__main__':
    shard = os.environ.get('RESEARCH_ROUND_TEST_SHARD')
    if shard:
        if shard not in ('0/4', '1/4', '2/4', '3/4'):
            raise SystemExit('invalid test shard')
        def cases(suite):
            for item in suite:
                if isinstance(item, unittest.TestSuite):
                    yield from cases(item)
                else:
                    yield item
        suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
        selected = list(cases(suite))[int(shard[0])::4]
        result = unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(selected))
        raise SystemExit(0 if result.wasSuccessful() else 1)
    unittest.main(verbosity=2)
