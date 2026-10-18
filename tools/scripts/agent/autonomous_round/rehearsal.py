"""Local carrier/seat fixture; only the existing readout make door executes."""
import copy
import json

from runtime import Stop, execute, utc


class Rehearsal:
    def __init__(self, root, make_readouts=False):
        self.root, self.now = root, 1800000000
        self.make_readouts = make_readouts
        self.revision, self.roles, self.writes = 'a' * 40, [], []
        self.carriers, self.verifications, self.issue_number = [], 0, 0
        self.lose_receipt = self.lose_before_write = self.interrupt_role = None
        self.fault = None
        self.other_unavailable = self.edit_prereg = False
        self.lock_fd = None

    def head(self, timeout=5):
        return self.revision

    def worker(self, role, payload, timeout):
        self.roles.append(role)
        self.now += 1
        if self.interrupt_role == role:
            raise KeyboardInterrupt()
        if self.fault and self.fault[0] == role:
            raise Stop(self.fault[1])
        if role == 'predict_other' and self.other_unavailable:
            raise Stop('NON_GPT_UNAVAILABLE')
        if role == 'generate':
            value = dict(event=dict(statement='0 + n = n', quantifiers='For every natural n'),
                surprise_threshold=0.25,
                candidate='Synthetic routing fixture; existing identity, no research novelty claim.')
        elif role.startswith('predict_'):
            assert set(payload) == {'event'}, 'prediction leaked solution context'
            value = {'probability': 0.75}
        elif role == 'solve':
            value = dict(status='ready', modules=['D5.Fixture'], summary='Synthetic solution.')
        else:
            value = dict(status='proved', proof_shape='bind-only',
                summary='Synthetic routing evidence; this is no new mathematical content.',
                successor='For every natural n, examine the same identity under a fresh test fixture.')
        other = role == 'predict_other'
        return dict(value=value, model='fixture-claude' if other else 'fixture-gpt',
                    model_family='Claude' if other else 'GPT')

    def find(self, intent, timeout):
        return [copy.deepcopy(x) for x in self.carriers if intent['marker'] in x['body']]

    def publish(self, intent, timeout):
        kind = intent['kind']
        self.writes.append(kind)
        if self.lose_before_write == kind:
            self.lose_before_write = None
            raise Stop('TRANSPORT_LOST')
        self.now += 1
        if kind == 'candidate':
            self.issue_number += 1
        url = f'https://github.com/the-omega-institute/trureturing/issues/{self.issue_number}'
        if kind != 'candidate':
            url += f'#issuecomment-{len(self.carriers) + 1}'
        carrier = dict(html_url=url, body=intent['body'], created_at=utc(self.now),
                       updated_at=utc(self.now), number=1)
        if self.edit_prereg and kind == 'preregister':
            carrier['updated_at'] = utc(self.now + 1)
        self.carriers.append(carrier)
        if self.lose_receipt == kind:
            self.lose_receipt = None
            raise Stop('TRANSPORT_LOST')
        return copy.deepcopy(carrier)

    def validate_prereg(self, carrier, prereg, timeout):
        from backend import validate_prereg
        validate_prereg(carrier, prereg)

    def check_commitment(self, issue, prereg, registered_at, candidate_sha256, timeout):
        from backend import check_commitment
        check_commitment([x for x in self.carriers if x['html_url'].split('#')[0] == issue],
                         prereg, registered_at, candidate_sha256)

    def verify(self, modules, head, timeout):
        self.verifications += 1
        self.now += 1

    def readouts(self, issue, as_of, timeout):
        carriers = [x for x in self.carriers if x['html_url'].split('#')[0] == issue]
        batch = dict(issues=[dict(issue=carriers[0], comments=carriers[1:])], evidence=[])
        if not self.make_readouts:
            from backend import readout_module
            return readout_module().recompute(batch, as_of)
        raw = execute(['make', '-s', '--no-print-directory', '-C', 'tools',
                       'research-readouts', 'AS_OF=' + as_of], self.root, timeout,
                      json.dumps(batch), self.lock_fd)
        return json.loads(raw)
