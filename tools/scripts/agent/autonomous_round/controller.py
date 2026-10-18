"""One active unit, immutable commitments, precharged seats and reconciled writes."""
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import re
import time
import uuid

from runtime import Limits, Stop, atomic, decode, locked, utc


def fence(kind, value):
    return '```research-' + kind + '-v1\n' + json.dumps(value, ensure_ascii=False) + '\n```'


def text(value):
    return isinstance(value, str) and bool(value.strip())


class Round:
    def __init__(self, path, backend, limits=None, clock=time.time, after_stage=None):
        self.path, self.backend = Path(path), backend
        self.limits, self.clock = limits or Limits(), clock
        self.after_stage = after_stage or (lambda stage: None)
        self.state, self.unit, self.wake = None, None, None
        self.readings = None

    def save(self):
        atomic(self.path, self.state)

    def result(self, status, detail=''):
        unit = self.unit or {}
        return dict(status=status, detail=detail, stage=unit.get('stage'),
                    unit=unit.get('id'), issue=unit.get('issue'),
                    terminal_status=unit.get('terminal_status'),
                    gaps=unit.get('gaps', []), calls=(self.state or {}).get('calls', 0),
                    readouts=self.readings)

    def run(self, wake_id):
        try:
            if not re.fullmatch(r'[A-Za-z0-9_.-]{1,100}', wake_id):
                raise Stop('WAKE_ID_REQUIRED', 'use a stable host invocation identity')
            with locked(self.path) as fd:
                self.backend.lock_fd = fd
                if hasattr(self.backend, 'clean_scratch'):
                    self.backend.clean_scratch()
                self.load(wake_id)
                if self.wake['done']:
                    return self.result('already_completed')
                if self.unit['stage'] == 'done':
                    self.wake['done'] = True
                    self.save()
                    return self.result('already_completed')
                if self.unit.get('inflight'):
                    self.recover_call()
                while self.unit['stage'] != 'done':
                    if self.io('head') != self.unit['head']:
                        raise Stop('HEAD_CHANGED', 'the pinned unit was not rebound')
                    if self.clock() >= self.wake['deadline']:
                        raise Stop('WAKE_DEADLINE')
                    try:
                        self.step()
                    except Stop as error:
                        if not self.close_boundary(error):
                            raise
                    self.save()
                    self.after_stage(self.unit['stage'])
                self.wake['done'] = True
                for wake in self.state['wakes'].values():
                    if wake.get('unit') == self.unit['id']:
                        wake['done'] = True
                self.save()
                return self.result('terminal')
        except Stop as error:
            return self.result(error.code, error.detail)

    def load(self, wake_id):
        if self.path.exists():
            self.state = decode(self.path.read_text())
            if self.state.get('version') != 1 or self.state.get('limits') != asdict(self.limits):
                raise Stop('CHECKPOINT_CONFLICT', 'version/limits differ; do not reset a unit')
        else:
            self.state = dict(version=1, limits=asdict(self.limits), calls=0,
                              wakes={}, active=None)
        wakes = self.state['wakes']
        if wake_id not in wakes:
            if len(wakes) >= self.limits.wakes:
                raise Stop('WAKE_BUDGET')
            wakes[wake_id] = dict(deadline=int(self.clock()) + self.limits.wake_seconds,
                                  calls=0, reserved_seconds=0, done=False, unit=None)
        self.wake = wakes[wake_id]
        previous = self.state['active']
        if self.wake.get('unit') and previous and self.wake['unit'] != previous['id']:
            self.wake['done'] = True
        if self.state['active'] is None or (self.state['active']['stage'] == 'done'
                                           and not self.wake['done']):
            if self.state['calls'] >= self.limits.total_calls:
                self.unit = previous
                self.save()
                raise Stop('TOTAL_CALL_BUDGET')
            predecessor = None if previous is None else previous['issue']
            self.state['active'] = dict(id=uuid.uuid4().hex,
                head=self.backend.head(timeout=self.reserve(5)), predecessor_issue=predecessor,
                deadline=int(self.clock()) + self.limits.unit_seconds, stage='generate',
                calls=0, reserved_seconds=0, gaps=[], inflight=None, intent=None,
                predictions=[], issue=None, prereg=None, execution_started_at=None)
        self.unit = self.state['active']
        self.wake['unit'] = self.unit['id']
        self.save()

    def reserve(self, seconds, model=False, mathematical=False):
        unit, wake, limits = self.unit, self.wake, self.limits
        if model:
            for used, cap, code in ((self.state['calls'], limits.total_calls, 'TOTAL_CALL_BUDGET'),
                                   (unit['calls'], limits.unit_calls, 'UNIT_CALL_BUDGET'),
                                   (wake['calls'], limits.wake_calls, 'WAKE_CALL_BUDGET')):
                if used >= cap:
                    raise Stop(code)
        remaining = min(seconds, wake['deadline'] - self.clock(),
                        limits.wake_seconds - wake['reserved_seconds'])
        if mathematical:
            remaining = min(remaining, unit['deadline'] - self.clock(),
                            limits.unit_seconds - unit['reserved_seconds'])
        if remaining <= 0:
            raise Stop('WALL_BUDGET')
        # An allocation is spent even if spawning fails or the controller restarts.
        wake['reserved_seconds'] += remaining
        if mathematical:
            unit['reserved_seconds'] += remaining
        if model:
            self.state['calls'] += 1
            unit['calls'] += 1
            wake['calls'] += 1
        self.save()
        return remaining

    def io(self, method, *args):
        return getattr(self.backend, method)(*args, timeout=self.reserve(5 if method == 'head' else 30))

    def worker(self, role, payload):
        seconds = self.reserve(self.limits.call_seconds, model=True, mathematical=True)
        self.unit['inflight'] = role
        self.save()
        try:
            answer = self.backend.worker(role, payload, timeout=seconds)
        except Stop:
            self.unit['inflight'] = None
            raise
        self.unit['inflight'] = None
        return answer

    def recover_call(self):
        # The supervisor held this same lock until the old seat and its deadline ended.
        unit, role = self.unit, self.unit['inflight']
        if role not in ('generate', 'predict_gpt', 'predict_other', 'solve', 'verify', 'evaluate'):
            raise Stop('CHECKPOINT_CONFLICT', 'unknown inflight role')
        unit['inflight'] = None
        unit['gaps'].append('CALL_OUTCOME_UNKNOWN: ' + role)
        if role.startswith('predict_'):
            if role == 'predict_other':
                unit['gaps'].append('NON_GPT_UNAVAILABLE: CALL_OUTCOME_UNKNOWN')
            self.advance('predict_other' if role == 'predict_gpt' else 'preregister')
        elif role == 'generate':
            unit.update(stage='done', terminal_status='invalid', boundary='CALL_OUTCOME_UNKNOWN')
        else:
            self.unresolved('CALL_OUTCOME_UNKNOWN: ' + role)
        self.save()

    def write(self, kind, body):
        unit = self.unit
        if unit['intent'] is None:
            digest = hashlib.sha256(body.encode()).hexdigest()
            marker = f'<!-- autonomous-research-action:{unit["id"]}:{kind}:{digest} -->'
            unit['intent'] = dict(kind=kind, body=body + '\n\n' + marker,
                                  marker=marker, attempted=False, issue=unit['issue'],
                                  since=utc(self.clock() - 60))
            self.save()
        intent = unit['intent']
        if intent['kind'] != kind:
            raise Stop('CHECKPOINT_CONFLICT', 'pending write belongs to another stage')
        found = self.io('find', intent)
        if found:
            if len(found) != 1 or found[0]['body'] != intent['body']:
                raise Stop('CARRIER_CONFLICT', intent['marker'])
            carrier = found[0]
        else:
            if intent['attempted']:
                raise Stop('WRITE_AMBIGUOUS', 'no distinguishable receipt; not resent')
            allocation = self.reserve(30)
            intent['attempted'] = True
            self.save()
            try:
                carrier = self.backend.publish(intent, timeout=allocation)
            except Stop as error:
                raise Stop('WRITE_UNKNOWN', error.code) from error
        if (carrier['body'] != intent['body'] or
                (kind != 'candidate' and carrier['updated_at'] != carrier['created_at'])):
            raise Stop('CARRIER_CONFLICT', 'carrier body/metadata changed')
        unit['intent'] = None
        return carrier

    def advance(self, stage):
        self.unit['stage'] = stage

    def step(self):
        unit, stage = self.unit, self.unit['stage']
        if stage == 'generate':
            answer = self.worker('generate', {'predecessor_issue': unit['predecessor_issue']})['value']
            event = answer.get('event')
            if (not isinstance(event, dict) or set(event) != {'statement', 'quantifiers'}
                    or not all(text(x) for x in event.values()) or not text(answer.get('candidate'))):
                raise Stop('WORKER_MALFORMED', 'candidate/event')
            self.no_blocks(answer['candidate'])
            threshold = answer.get('surprise_threshold')
            if type(threshold) not in (int, float) or not 0 <= threshold <= 1:
                raise Stop('WORKER_MALFORMED', 'surprise_threshold')
            unit.update(event=event, threshold=threshold,
                        draft=answer['candidate'], stage='candidate')
        elif stage == 'candidate':
            carrier = self.write('candidate', unit.get('draft', ''))
            unit['issue'] = carrier['html_url']
            unit['candidate_sha256'] = hashlib.sha256(carrier['body'].encode()).hexdigest()
            unit.pop('draft', None)
            self.advance('predict_gpt')
        elif stage in ('predict_gpt', 'predict_other'):
            try:
                # No candidate, source issue, generated proof, workspace or other seat output.
                answer = self.worker(stage, {'event': unit['event']})
                value = answer['value'].get('probability')
                if type(value) not in (int, float) or not 0 <= value <= 1:
                    raise Stop('WORKER_MALFORMED', 'probability')
                family = answer['model_family']
                if not text(answer.get('model')) or not text(family):
                    raise Stop('WORKER_MALFORMED', 'missing carrier model attribution')
                if stage == 'predict_other' and family == 'GPT':
                    raise Stop('NON_GPT_UNAVAILABLE', 'carrier returned GPT')
                unit['predictions'].append(dict(seat=stage, model_family=family,
                    event=unit['event'], probability=value))
            except Stop as error:
                if error.code.endswith('BUDGET') or error.code == 'WALL_BUDGET':
                    raise
                unit['gaps'].append(('NON_GPT_UNAVAILABLE' if stage == 'predict_other'
                                      else 'PREDICTION_UNAVAILABLE') + ': ' + error.code)
            self.advance('predict_other' if stage == 'predict_gpt' else 'preregister')
        elif stage == 'preregister':
            if unit['prereg'] is None:
                unit['prereg'] = dict(event=unit['event'], deadline=utc(unit['deadline']),
                    scoring_rule={'name': 'binary-brier', 'version': 1},
                    surprise_threshold=unit['threshold'], predictions=unit['predictions'])
            if self.clock() >= unit['deadline']:
                raise Stop('UNIT_DEADLINE', 'execution did not start')
            carrier = self.write('preregister', fence('prereg', unit['prereg']))
            self.io('validate_prereg', carrier, unit['prereg'])
            unit['registered_at'] = carrier['created_at']
            unit['prereg_url'] = carrier['html_url']
            self.advance('solve')
        elif stage == 'solve':
            if self.clock() >= unit['deadline']:
                raise Stop('UNIT_DEADLINE', 'no post-deadline execution')
            commitment = self.check_commitment()
            if unit['execution_started_at'] is None:
                if utc(self.clock()) < unit['registered_at']:
                    raise Stop('CLOCK_PRECEDES_REGISTRATION')
                unit['execution_started_at'] = utc(self.clock())
                self.save()
            try:
                answer = self.worker('solve', dict(issue=unit['issue'], head=unit['head'],
                    event=unit['event'], deadline=utc(unit['deadline']),
                    commitment=commitment))['value']
                if answer.get('status') not in ('ready', 'unresolved') or not text(answer.get('summary')):
                    raise Stop('WORKER_MALFORMED', 'solve result')
                unit['solution'] = answer
                self.advance('verify' if answer['status'] == 'ready' else 'evidence')
                if answer['status'] == 'unresolved':
                    self.unresolved(answer['summary'])
            except Stop as error:
                if error.code.endswith('BUDGET') or error.code == 'WALL_BUDGET':
                    raise
                self.unresolved(error.code)
        elif stage == 'verify':
            self.check_commitment()
            try:
                seconds = self.reserve(900, mathematical=True)
                self.io_validate_modules(unit['solution'].get('modules'))
                unit['inflight'] = 'verify'
                self.save()
                self.backend.verify(unit['solution']['modules'], unit['head'], timeout=seconds)
                unit['inflight'] = None
                self.advance('evaluate')
            except Stop as error:
                unit['inflight'] = None
                self.unresolved(error.code)
        elif stage == 'evaluate':
            commitment = self.check_commitment()
            try:
                answer = self.worker('evaluate', dict(issue=unit['issue'], event=unit['event'],
                    commitment=commitment, solution=unit['solution'],
                    checks='scoped Lean report and make gate exited 0'))['value']
                if (answer.get('status') not in ('proved', 'refuted', 'unresolved', 'invalid')
                        or answer.get('proof_shape') not in ('content', 'bind-only', None)
                        or not text(answer.get('summary')) or not text(answer.get('successor'))):
                    raise Stop('WORKER_MALFORMED', 'evaluation')
                unit['evaluation'] = answer
                unit['terminal_status'] = answer['status']
                unit['settled_at'] = (utc(self.clock())
                    if answer['status'] in ('proved', 'refuted') else None)
                if self.clock() >= unit['deadline']:
                    self.unresolved('EVALUATION_AFTER_DEADLINE')
                self.advance('evidence')
            except Stop as error:
                if error.code.endswith('BUDGET') or error.code == 'WALL_BUDGET':
                    raise
                self.unresolved(error.code)
        elif stage == 'evidence':
            answer = unit['evaluation']
            self.no_blocks(answer['summary'])
            self.no_blocks(answer['successor'])
            shape = ('proof_shape: ' + answer['proof_shape']
                     if answer['proof_shape'] and unit['settled_at'] else '')
            body = answer['summary'] + '\n' + shape + '\n\nSuccessor:\n' + answer['successor']
            if unit['gaps']:
                body += '\n\nCapability gaps:\n' + '\n'.join(unit['gaps'])
            carrier = self.write('evidence', body)
            unit['evidence'] = dict(url=carrier['html_url'], excerpt=answer['summary'])
            unit['shape_evidence'] = dict(url=carrier['html_url'], excerpt=shape) if shape else None
            unit.pop('solution', None)
            unit.pop('evaluation', None)
            self.advance('terminal')
        elif stage == 'terminal':
            terminal = dict(event=unit['event'], execution_started_at=unit['execution_started_at'],
                status=unit['terminal_status'], settled_at=unit['settled_at'],
                evidence=unit['evidence'], shape_evidence=unit['shape_evidence'])
            self.write('terminal', fence('terminal', terminal))
            self.advance('readouts')
        elif stage == 'readouts':
            if unit['terminal_status'] in ('unresolved', 'invalid') and self.clock() < unit['deadline']:
                raise Stop('WAIT_DEADLINE', 'readouts requires the registered cutoff')
            self.readings = self.io('readouts', unit['issue'], utc(self.clock()))
            self.advance('done')
        elif stage == 'unexecuted':
            body = (unit['boundary'] + '\nNo substantive execution started; no binary answer or '
                    'execution timestamp is asserted.\n\nSuccessor:\n'
                    'Reassess the exact event and named resource boundary in a fresh preregistration.')
            self.write('boundary', body)
            self.advance('readouts' if unit['prereg'] is not None else 'done')
        else:
            raise Stop('CHECKPOINT_CONFLICT', 'unknown phase ' + str(stage))

    def unresolved(self, reason):
        self.unit.update(terminal_status='unresolved', settled_at=None, stage='evidence',
            evaluation=dict(status='unresolved', proof_shape=None, summary=reason,
                successor='Resolve the named obstacle for the exact event under a fresh preregistration.'))

    def check_commitment(self):
        unit = self.unit
        return self.io('check_commitment', unit['issue'], unit['prereg'], unit['registered_at'],
                       unit['candidate_sha256'], unit.get('prereg_url'))

    def close_boundary(self, error):
        unit = self.unit
        if unit['intent'] is not None or unit['stage'] not in (
                'generate', 'candidate', 'predict_gpt', 'predict_other', 'preregister', 'solve', 'evaluate'):
            return False
        exhausted = (error.code in ('UNIT_CALL_BUDGET', 'TOTAL_CALL_BUDGET', 'UNIT_DEADLINE')
            or (error.code == 'WALL_BUDGET' and (self.clock() >= unit['deadline']
                or unit['reserved_seconds'] >= self.limits.unit_seconds)))
        if not exhausted:
            return False
        unit['gaps'].append(error.code)
        if unit['execution_started_at'] is not None:
            self.unresolved(error.code)
        else:
            # No fabricated execution time and no synthetic strict terminal for an unexecuted unit.
            unit.update(terminal_status='invalid', boundary=error.code,
                        stage='unexecuted' if unit['issue'] else 'done')
        return True

    @staticmethod
    def no_blocks(body):
        if re.search(r'(?m)^```research-', body):
            raise Stop('WORKER_MALFORMED', 'result exposition cannot contain strict carrier blocks')

    @staticmethod
    def io_validate_modules(modules):
        if (not isinstance(modules, list) or not modules
                or not all(isinstance(x, str) and re.fullmatch(r'(D5|Reg)\.[A-Za-z0-9_.]+', x)
                           for x in modules) or len(set(modules)) != len(modules)):
            raise Stop('WORKER_MALFORMED', 'nonempty D5/Reg module domain required')
