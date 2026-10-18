"""Local transport contracts for checked inputs and malformed carrier responses."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from backend import Backend
from controller import Round
from rehearsal import Rehearsal
from runtime import Stop
from workers import Workers


ROOT = Path(__file__).resolve().parents[4]
CANDIDATE = ('Definition: PRIVATE_GENERATED_PROOF uses relation R.\n'
             'Source: original S; readout: rho; task: T; layer: L.\n'
             'Proposed witness: R(x,y) separates the fixed task fiber.')


class WorkerInputTests(unittest.TestCase):
    def exercise(self, change=None):
        backend, production = Rehearsal(ROOT), Backend(ROOT)
        prompts = {}

        def gh(route, timeout, paginate=False):
            if paginate:
                return copy.deepcopy(backend.carriers[1:])
            return copy.deepcopy(backend.carriers[0])

        def transport(argv, cwd, timeout, stdin='', lock_fd=None):
            if argv[0] == 'claude':
                role = 'predict_other'
                answer = json.dumps({'result': '{"probability":0.6}',
                                     'modelUsage': {'claude-fixture': {}}})
            elif argv[0].endswith('python3') or 'nyx.py' in argv[1]:
                role = 'generate'
                prompts[role] = Path(argv[3]).read_text()
                Path(argv[4]).write_text(json.dumps(dict(candidate=CANDIDATE,
                    event=dict(statement='P', quantifiers='For every x'), surprise_threshold=0.25)))
                Path(argv[4] + '.status.json').write_text(
                    json.dumps({'model': {'model_label': 'chatgpt-6-pro'}}))
                return ''
            else:
                contract = json.loads(Path(argv[argv.index('--output-schema') + 1]).read_text())
                props = contract['properties']
                role = 'predict_gpt' if 'probability' in props else (
                    'solve' if 'modules' in props else 'evaluate')
                value = dict(probability=0.6) if role == 'predict_gpt' else (
                    dict(status='ready', modules=['D5.Fixture'], summary='Local solution.')
                    if role == 'solve' else dict(status='proved', proof_shape='content',
                        summary='Local fidelity evidence.', successor='For every x, test Q(x).'))
                Path(argv[argv.index('--output-last-message') + 1]).write_text(json.dumps(value))
                answer = ''
                if role == 'solve':
                    self.assertIn('sandbox_workspace_write.network_access=false', argv)
            prompts[role] = stdin
            return answer

        backend.worker = production.worker
        backend.check_commitment = production.check_commitment
        production.gh = gh
        with tempfile.TemporaryDirectory() as name, patch('workers.execute', side_effect=transport):
            path = Path(name) / 'checkpoint.json'
            def changed(stage):
                if stage == 'solve' and change:
                    change(backend, path)
            result = Round(path, backend, clock=lambda: backend.now, after_stage=changed).run('wake')
        return result, prompts, backend

    def test_checked_full_candidate_and_prereg_reach_only_solver_and_evaluator(self):
        result, prompts, backend = self.exercise()
        self.assertEqual('terminal', result['status'])
        for role in ('solve', 'evaluate'):
            payload = json.loads(prompts[role].split('\nInput:\n')[1].split('\nSchema:\n')[0])
            checked = payload['commitment']
            self.assertEqual(backend.carriers[0]['body'], checked['candidate']['body'])
            self.assertIn(CANDIDATE, checked['candidate']['body'])
            self.assertEqual(backend.carriers[1], checked['preregistration'])
            self.assertIn('```research-prereg-v1', checked['preregistration']['body'])
            self.assertEqual(payload['event'], checked['prereg']['event'])
            self.assertEqual(hashlib.sha256(checked['candidate']['body'].encode()).hexdigest(),
                             checked['candidate_sha256'])
        for role in ('predict_gpt', 'predict_other'):
            payload = json.loads(prompts[role].split('\n')[-1])
            self.assertEqual({'event': {'statement': 'P', 'quantifiers': 'For every x'}}, payload)
            self.assertNotIn('PRIVATE_GENERATED_PROOF', prompts[role])

    def test_changed_candidate_or_registration_identity_is_rejected_before_solver(self):
        def candidate(backend, path):
            backend.carriers[0]['body'] += '\nDifferent witness'
        def issue(backend, path):
            backend.carriers[0]['html_url'] += '9'
        def registration(backend, path):
            backend.carriers[1]['html_url'] += '9'
        def event(backend, path):
            backend.carriers[1]['body'] = backend.carriers[1]['body'].replace('For every x', 'Some x')
        for change in (candidate, issue, registration, event):
            with self.subTest(change=change.__name__):
                result, prompts, _ = self.exercise(change)
                self.assertIn(result['status'], ('CARRIER_CONFLICT', 'CARRIER_IDENTITY'))
                self.assertNotIn('solve', prompts)
                self.assertNotIn('evaluate', prompts)


class MalformedWorkerTests(unittest.TestCase):
    def test_zero_exit_missing_or_nonobject_artifacts_are_named_in_the_same_call(self):
        cases = [('generate', 'missing'), ('generate', 'missing-status'),
                 ('generate', 'status-array'), ('generate', 'model-array'),
                 ('generate', 'answer-array'), ('solve', 'missing'),
                 ('solve', 'answer-array'), ('evaluate', 'answer-array'),
                 ('predict_gpt', 'missing'), ('predict_other', 'carrier-array'),
                 ('predict_other', 'usage-array'), ('predict_other', 'answer-array')]
        for role, fault in cases:
            with self.subTest(role=role, fault=fault), tempfile.TemporaryDirectory() as name:
                worker = Workers(Path(name))
                def transport(argv, timeout, stdin='', cwd=None):
                    if role == 'predict_other':
                        if fault == 'carrier-array':
                            return '[]'
                        return json.dumps({'result': '[]' if fault == 'answer-array' else '{}',
                            'modelUsage': ['claude-fixture'] if fault == 'usage-array'
                            else {'claude-fixture': {}}})
                    output = Path(argv[4] if role == 'generate' else
                                  argv[argv.index('--output-last-message') + 1])
                    if fault != 'missing':
                        output.write_text('[]' if fault == 'answer-array' else '{}')
                    if role == 'generate' and fault not in ('missing', 'missing-status'):
                        status = [] if fault == 'status-array' else {'model':
                            [] if fault == 'model-array' else {'model_label': 'chatgpt-6-pro'}}
                        Path(str(output) + '.status.json').write_text(json.dumps(status))
                    return ''
                worker.call = transport
                with self.assertRaisesRegex(Stop, 'WORKER_MALFORMED'):
                    worker.worker(role, {'event': {'statement': 'P', 'quantifiers': 'All x'}}, 5)

    def test_missing_generation_artifact_returns_named_round_stop_without_traceback(self):
        with tempfile.TemporaryDirectory() as name:
            backend = Rehearsal(ROOT)
            production = Workers(Path(name))
            production.call = lambda *args, **kwargs: ''
            backend.worker = production.worker
            result = Round(Path(name) / 'checkpoint.json', backend,
                           clock=lambda: backend.now).run('wake')
            self.assertEqual('WORKER_MALFORMED', result['status'])
            self.assertEqual([], backend.writes)
