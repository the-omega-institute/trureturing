#!/usr/bin/env python3
"""Record Lake's invocation-local project build actions, never artifact hashes."""
import json
import os
from pathlib import Path
import re
import sys
import tempfile

BUILT = re.compile(r'^[^\s]+ \[[0-9]+/[0-9]+\](?: \(Optional\))? Built ([^\s:]+)')
COMPLETED = re.compile(r'^Build completed successfully \([0-9]+ jobs?\)\.$', re.MULTILINE)


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
            if (not isinstance(row, dict) or row.get('kind') not in ('extract', 'aggregate')
                    or type(row.get('count')) is not int or row['count'] < 0):
                raise ValueError('invalid native build activity')
            if row['count'] > 0:
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
        record(*(Path(argument) for argument in sys.argv[1:4]), *sys.argv[4:])
    except (OSError, ValueError, TypeError) as error:
        print('LEAN_BUILD_WORK_UNKNOWN ' + str(error), file=sys.stderr)
        sys.exit(2)
