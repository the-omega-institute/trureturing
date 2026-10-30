#!/usr/bin/env python3
"""Record Lake's invocation-local project build actions, never artifact hashes."""
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import subprocess
import uuid
import tempfile

BUILT = re.compile(r'^[^\s]+ \[[0-9]+/[0-9]+\](?: \(Optional\))? Built ([^\s:]+)')
COMPLETED = re.compile(r'^Build completed successfully \([0-9]+ jobs?\)\.$', re.MULTILINE)
FIB_KINDS = ('extracted', 'generated', 'reused', 'unavailable',
             'analysis-invocations', 'analysis-ns')


def observations(logs, phases):
    """Current direct observations, independent of Lake's replayable output.

    Reused artifacts were not extracted or analyzed by this invocation. Their
    population is deliberately not counted as invocation-local reused work.
    """
    counts = dict.fromkeys(FIB_KINDS, 0)
    try:
        if 'report' in phases:
            if (logs / 'report.exit.log').read_text().strip() != '0':
                raise ValueError('incomplete report activity')
            for line in (logs / 'native-work.jsonl').read_text().splitlines():
                row = json.loads(line)
                if not isinstance(row, dict):
                    raise ValueError('invalid native build activity')
                if row.get('kind', '').startswith('fib-'):
                    key = row['kind'][4:]
                    if key not in counts or type(row.get('count')) is not int or row['count'] < 0:
                        raise ValueError('invalid FIB activity')
                    counts[key] += row['count']
        scope = 'invocation-local'
    except (OSError, ValueError, TypeError, AttributeError):
        counts = dict.fromkeys(FIB_KINDS)
        scope = 'unavailable'
    print('LEAN_INSPECTOR_FIB_WORK ' + json.dumps(dict(scope=scope, **counts), sort_keys=True), flush=True)
    try:
        timing = {}
        path = logs / 'native-phases.jsonl'
        if 'report' in phases and not path.is_file():
            raise ValueError('missing native phase activity')
        for line in path.read_text().splitlines() if path.exists() else ():
            row = json.loads(line)
            boundary = row['boundary']
            if boundary not in ('duration', 'start', 'finish'):
                continue
            item = timing.setdefault(row['phase'], dict(started=0, finished=0, elapsed_ns=0))
            if boundary == 'duration':
                item['started'] += 1
                item['finished'] += 1
                item['elapsed_ns'] += row['elapsed_ns']
            elif boundary in ('start', 'finish'):
                item['started' if boundary == 'start' else 'finished'] += 1
                item['elapsed_ns'] += row['monotonic_ms'] * 1_000_000 * (-1 if boundary == 'start' else 1)
        for item in timing.values():
            if item['started'] != item['finished'] or item['elapsed_ns'] < 0:
                item['elapsed_ns'] = None
        print('LEAN_INSPECTOR_TIMING ' + json.dumps(timing, sort_keys=True), flush=True)
    except (OSError, ValueError, KeyError, TypeError):
        print('LEAN_INSPECTOR_TIMING_UNAVAILABLE', flush=True)



def export_observations(root, logs, report, inspector_exit, *phases):
    """Export invocation-local raw telemetry to the caller's captured log.

    Binding and stream trailers make missing/truncated transport distinguishable
    from an empty stream. These observations never decide report acceptance.
    """
    invocation = uuid.uuid4().hex
    def emit(kind, **fields):
        print('LEAN_INSPECTOR_OBSERVATION ' + json.dumps(dict(
            schema='stratalint-native-observations-v1', invocation_id=invocation,
            kind=kind, **fields), sort_keys=True), flush=True)
    checkout = None
    try:
        checkout = subprocess.run(['git', '-C', str(root), 'rev-parse', '--verify', 'HEAD'],
            capture_output=True, text=True, check=True, timeout=5).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    report_hash = None
    try:
        digest = hashlib.sha256()
        with report.open('rb') as source:
            for chunk in iter(lambda: source.read(1024 * 1024), b''):
                digest.update(chunk)
        report_hash = digest.hexdigest()
    except OSError:
        pass
    emit('binding', repository=str(root.resolve()), checkout_sha=checkout,
         github_sha=os.environ.get('GITHUB_SHA'), run_id=os.environ.get('GITHUB_RUN_ID'),
         run_attempt=os.environ.get('GITHUB_RUN_ATTEMPT'), job=os.environ.get('GITHUB_JOB'),
         workflow_ref=os.environ.get('GITHUB_WORKFLOW_REF'),
         event=os.environ.get('GITHUB_EVENT_NAME'), report=str(report.resolve()),
         report_sha256=report_hash, inspector_exit=int(inspector_exit), phases=phases)
    for name in ('native-phases.jsonl', 'native-work.jsonl'):
        count, digest = 0, hashlib.sha256()
        try:
            with (logs / name).open('rb') as source:
                for count, raw in enumerate(source, 1):
                    digest.update(raw)
                    # Preserve every raw field and incomplete/malformed line.
                    # JSON encoding prevents a raw line becoming a log command.
                    emit('record', stream=name, line=count, raw=raw.decode('utf-8'))
            emit('stream-end', stream=name, lines=count, sha256=digest.hexdigest(), status='complete')
        except (OSError, UnicodeError) as error:
            emit('stream-end', stream=name, lines=count, sha256=None,
                 status='unavailable', error=str(error))
    emit('end')


def output_names(directory):
    """Map native compiler output addresses to Lake's module/target captions."""
    names = set()
    for base, _, files in os.walk(directory):
        path = Path(base)
        for name in files:
            if name.endswith('.olean') and '/lib/lean/' in str(path) + '/':
                prefix = (str(path) + '/').split('/lib/lean/', 1)[1]
                names.add((prefix + name[:-6]).replace('/', '.'))
            elif path.name == 'bin' and '.' not in name:
                names.add(name)
    return names


def phase_work(root, logs, phase, project_names):
    if not (logs / (phase + '.exit.log')).exists():
        return None
    if (logs / (phase + '.exit.log')).read_text().strip() != '0':
        return None
    text = '\n'.join((logs / (phase + '.' + stream + '.log')).read_text()
                     for stream in ('stdout', 'stderr'))
    if not COMPLETED.search(text):
        return None
    count, unknown = 0, False
    packages = list((root / '.lake/packages').glob('*'))
    for line in text.splitlines():
        match = BUILT.match(line)
        if not match:
            continue
        caption = match[1]
        name = caption.rsplit('/', 1)[-1]
        if name in project_names():
            count += 1
        elif any((package / '.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')).is_file()
                 or (package / '.lake/build/bin' / name).is_file() for package in packages):
            continue
        else:
            unknown = True
    # A positive count is an established lower bound even if another target's
    # address cannot be resolved. Zero requires complete classification.
    return count if count or not unknown else None


def record(root, logs, destination, *phases):
    observations(logs, phases)
    from functools import lru_cache
    @lru_cache(maxsize=1)
    def names():
        return output_names(root / '.lake/build')
    value = dict(schema_version=1, run_id=os.environ.get('GITHUB_RUN_ID', ''),
                 run_attempt=os.environ.get('GITHUB_RUN_ATTEMPT', ''), repository=str(root.resolve()),
                 report=phase_work(root, logs, 'report', names) if 'report' in phases else 0,
                 programs=phase_work(root, logs, 'programs', names) if 'programs' in phases else 0)
    if 'report' in phases:
        activity = logs / 'native-work.jsonl'
        for line in activity.read_text().splitlines():
            row = json.loads(line)
            if (not isinstance(row, dict) or row.get('kind') not in
                    ('extract', 'aggregate', *('fib-' + key for key in FIB_KINDS))
                    or type(row.get('count')) is not int or row['count'] < 0):
                raise ValueError('invalid native build activity')
            if row['kind'].startswith('fib-'):
                continue
            elif row['count'] > 0:
                value['report'] = (value['report'] or 0) + row['count']
    destination.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix='.build-work-', dir=destination.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, 'w') as stream:
            json.dump(value, stream)
            stream.write('\n')
        temporary.replace(destination)
    finally:
        temporary.unlink(missing_ok=True)
    print('LEAN_BUILD_WORK ' + json.dumps(value, sort_keys=True), flush=True)


if __name__ == '__main__':
    try:
        if sys.argv[1:2] == ['--export']:
            export_observations(*(Path(argument) for argument in sys.argv[2:5]), *sys.argv[5:])
        elif sys.argv[1:2] == ['--observations']:
            observations(Path(sys.argv[2]), sys.argv[3:])
        else:
            record(*(Path(argument) for argument in sys.argv[1:4]), *sys.argv[4:])
    except (OSError, ValueError, TypeError) as error:
        print('LEAN_BUILD_WORK_UNKNOWN ' + str(error), file=sys.stderr)
        sys.exit(2)
