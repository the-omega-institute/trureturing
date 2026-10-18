"""A bounded wake entry. The host owns subsequent invocations."""
import argparse
import json
from pathlib import Path
import signal
import tempfile

from backend import Backend
from controller import Round
from rehearsal import Rehearsal
from runtime import Stop, locked

ROOT = Path(__file__).resolve().parents[4]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('live', 'dry-run', 'probe'), default='live')
    parser.add_argument('--wake', default='')
    args = parser.parse_args()
    state_dir = ROOT / '.lake/autonomous-research-round'
    state_dir.mkdir(parents=True, exist_ok=True)
    if args.mode == 'dry-run':
        with tempfile.TemporaryDirectory(dir=state_dir) as name:
            backend = Rehearsal(ROOT, make_readouts=True)
            result = Round(Path(name) / 'checkpoint.json', backend,
                           clock=lambda: backend.now).run('synthetic-wake')
            result['route'] = dict(carrier='local REST fixture; no external writes',
                roles=backend.roles, verify='local fixture; no Lean verification claimed',
                readouts='make -C tools research-readouts (actual strict parser)',
                production_generation='python3 tools/scripts/agent/nyx/nyx.py ask',
                production_execution='codex exec < promptfile; make lean-report-scoped; make gate')
    elif args.mode == 'probe':
        try:
            # Share the live seat lock. A capability probe is not a research unit or a prediction.
            with locked(state_dir / 'checkpoint.json') as fd:
                backend = Backend(ROOT)
                backend.lock_fd = fd
                answer = backend.worker('predict_other', {'event': {
                    'statement': '2 + 2 = 4', 'quantifiers': 'In the natural numbers'}}, timeout=60)
                result = dict(status='available', path='Claude CLI --print --model sonnet',
                              model=answer['model'], model_family=answer['model_family'],
                              response=answer['value'])
        except Stop as error:
            result = dict(status='unavailable', path='Claude CLI --print --model sonnet',
                          reason=error.code, detail=error.detail)
    else:
        result = Round(state_dir / 'checkpoint.json', Backend(ROOT)).run(args.wake)
    print(json.dumps(result, ensure_ascii=False, allow_nan=False))
    return 0 if result['status'] in ('terminal', 'already_completed', 'available') else 2


if __name__ == '__main__':
    def interrupted(signum, frame):
        raise KeyboardInterrupt()
    signal.signal(signal.SIGTERM, interrupted)
    raise SystemExit(main())
