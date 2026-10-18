"""Fresh carrier calls with role-specific schemas and attribution from the carrier."""
import json
import os
from pathlib import Path
import sys
import tempfile

from runtime import Stop, decode, execute

REPOSITORY = 'https://github.com/the-omega-institute/trureturing'
REASONING = '深入思考与推理, 如数学推理按照正式定义定理证明推理'


def schema(role):
    string = {'type': 'string'}
    if role.startswith('predict_'):
        props = {'probability': {'type': 'number', 'minimum': 0, 'maximum': 1}}
    elif role == 'generate':
        props = dict(event={'type': 'object', 'properties': dict(statement=string, quantifiers=string),
                            'required': ['statement', 'quantifiers'], 'additionalProperties': False},
                     candidate=string, surprise_threshold={'type': 'number', 'minimum': 0, 'maximum': 1})
    elif role == 'solve':
        props = dict(status={'type': 'string', 'enum': ['ready', 'unresolved']},
                     modules={'type': 'array', 'items': string}, summary=string)
    else:
        props = dict(status={'type': 'string', 'enum': ['proved', 'refuted', 'invalid', 'unresolved']},
                     proof_shape={'type': ['string', 'null'], 'enum': ['content', 'bind-only', None]},
                     summary=string, successor=string)
    return dict(type='object', properties=props, required=list(props), additionalProperties=False)


def prompt(role, payload):
    if role.startswith('predict_'):
        return ('Independent prediction. Only this event is disclosed. Do not access project files, '
                'other seats, candidate proofs or the issue. Predict its truth probability before '
                'substantive execution. Return only JSON {"probability":number}.\n' + json.dumps(payload))
    common = (REASONING + '\n' + REPOSITORY + '\n'
        'Follow CLAUDE.md and the current autonomous-research skill. Do not spawn seats, commit, '
        'publish, send messages, write issues/comments/PRs, or change harness/skills/spec/CLAUDE.md. '
        'Only the controller owns external writes. Return exactly the supplied JSON schema.\n')
    if role == 'generate':
        task = ('Directly reason at the research frontier and generate a substantive candidate result; '
            'do not select from digestion atoms or a topic queue. Supply full definitions, quantified '
            'theorem/construction, assumptions and proof, proposed live-path non-binding facts, '
            'admission/use justification and source-faithful Application obligations. On the same '
            'result propose both P (independent content/escape witness) and I (preregistered '
            'task-related information target: capture or boundary route). State original source, '
            'readout, task, layer and proposed witnesses; keep identity/duplicate/unrelated-coordinate '
            'controls separate. Zero delta and endpoint epsilon are not rejection gates. '
            'Check repository/mathlib/literature reuse before claiming novelty; unread sources are '
            'unverified, suspected-novel requires original-source due diligence, never global novelty. '
            'Do not do directed formalization yet. The event and threshold will be fixed unchanged '
            'before isolated prediction and execution. The carrier cannot run Lean; supply complete '
            'mathematics for downstream codex to check. candidate is result exposition, not a diary.')
    elif role == 'solve':
        task = ('Read the candidate issue and its unchanged preregistration. Apply the existing '
            'codex-formalize route, repository-first reuse, exact existing make doors, D5/Scribe/Reg '
            'and normal admission/use rules. No bind-only filler. Do not alter the fixed event, '
            'prediction, deadline, source/readout/task/layer. Formalize only this unit in this worktree. '
            'Use make for builds/checks; do not publish research or open a PR. Return ready only with '
            'actual nonempty D5/Reg module names; otherwise unresolved and the precise obstacle. '
            'The controller subsequently runs the scoped report and gate independently.')
    else:
        task = ('Independently evaluate the exact event and current formalization after successful '
            'scoped report and normal gate. Read source, live proof paths, assumptions, literature '
            'attribution, §3.2 escape/admission and §3.3 use; oracle is not validation. Distinguish '
            'P from I; report missing Application/FIB evidence explicitly, do not invent numeric '
            'fib_analysis. A proof of a different event is invalid. A compiler success alone does '
            'not establish fidelity, content or novelty. Return the mathematical settlement, actual '
            'proof shape, result/boundaries and a fully quantified successor with assumptions. '
            'No edits or external writes. summary contains only reusable results/evidence/boundaries.')
    return common + task + '\nInput:\n' + json.dumps(payload, ensure_ascii=False) + '\nSchema:\n' + json.dumps(schema(role))


class Workers:
    def __init__(self, root):
        self.root, self.lock_fd = Path(root), None
        self.scratch = self.root / '.lake' / 'autonomous-research-round' / 'scratch'
        self.scratch.mkdir(parents=True, exist_ok=True)

    def call(self, argv, timeout, stdin='', cwd=None):
        return execute(argv, cwd or self.root, timeout, stdin, self.lock_fd)

    def worker(self, role, payload, timeout):
        with tempfile.TemporaryDirectory(dir=self.scratch) as name:
            scratch = Path(name)
            message = prompt(role, payload)
            if role == 'generate':
                brief, output = scratch / 'brief.txt', scratch / 'answer.txt'
                brief.write_text(message)
                self.call([sys.executable, str(self.root / 'tools/scripts/agent/nyx/nyx.py'),
                           'ask', str(brief), str(output)], timeout)
                status = decode(Path(str(output) + '.status.json').read_text())
                model = (status.get('model') or {}).get('model_label')
                if not isinstance(model, str) or not model:
                    raise Stop('WORKER_MALFORMED', 'oracle attribution missing')
                answer = dict(value=decode(output.read_text()), model=model, model_family='GPT')
            elif role == 'predict_other':
                raw = self.call(['claude', '--print', '--model', 'sonnet',
                    '--output-format', 'json', '--tools', '', '--no-session-persistence',
                    '--disable-slash-commands', '--strict-mcp-config', '--mcp-config',
                    '{"mcpServers":{}}', '--setting-sources', '', '--system-prompt',
                    'Independent event prediction. Use only the event supplied on stdin.'],
                    timeout, message, scratch)
                carrier = decode(raw)
                models = list((carrier.get('modelUsage') or {}).keys())
                if carrier.get('is_error') or len(models) != 1 or not models[0].startswith('claude-'):
                    raise Stop('NON_GPT_UNAVAILABLE', 'no attributable Claude response')
                answer = dict(value=decode(carrier.get('result')), model=models[0], model_family='Claude')
            else:
                contract, output = scratch / 'schema.json', scratch / 'answer.json'
                contract.write_text(json.dumps(schema(role)))
                readonly = role != 'solve'
                argv = ['codex', 'exec', '--model', 'gpt-6', '--skip-git-repo-check',
                    '--sandbox', 'read-only' if readonly else 'workspace-write',
                    '-c', 'approval_policy="never"', '-c', 'features.multi_agent=false',
                    '-c', 'sandbox_workspace_write.network_access=false',
                    '-c', 'mcp_servers={}', '--output-schema', str(contract),
                    '--output-last-message', str(output)]
                if role.startswith('predict_'):
                    argv += ['-c', 'project_doc_max_bytes=0']
                self.call(argv, timeout, message, scratch if role.startswith('predict_') else self.root)
                answer = dict(value=decode(output.read_text()), model='gpt-6', model_family='GPT')
            if not isinstance(answer['value'], dict):
                raise Stop('WORKER_MALFORMED', 'seat result must be a JSON object')
            return answer
