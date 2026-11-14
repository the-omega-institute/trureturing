#!/usr/bin/env python3
"""Consume the FILEMAP-registered report input declaration.

Lake owns compilation. This reader only expands authored path sets; Lake owns dependency and invalidation semantics.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import subprocess
import tempfile

MANIFEST = 'lean-report-inputs.json'
LOADER = 'tools/scripts/report/lean-report-selection.py'
REPORT_FORMAT = 'stratalint-raw-lean-report-v4'
SCOPES = ('lean-report', 'scribe-content')
# The report entry supports this one explicit execution contract. Extending
# semantic inputs requires a registration/code change, never host discovery.
REPORT_EXECUTION = {
    'tools': ('lake', 'lean'),
    'platform': ('system', 'machine'),
    'environment': ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'ELAN_TOOLCHAIN', 'LEAN_OPTS'),
}


def fail(location, message):
    raise ValueError(f'{MANIFEST}: {location}: {message}')


def fields(value, expected, location):
    if not isinstance(value, dict) or set(value) != set(expected):
        actual = sorted(value) if isinstance(value, dict) else type(value).__name__
        fail(location, f'expected fields {sorted(expected)}, got {actual}')


def validate_pattern(pattern, location):
    if (not isinstance(pattern, str) or not pattern or pattern != pattern.strip()
            or pattern.startswith('/') or '\\' in pattern or '?' in pattern
            or any(ord(c) < 32 or ord(c) > 126 for c in pattern)
            or any(p in ('', '.', '..') for p in pattern.split('/'))):
        fail(location, f'unsafe path pattern {pattern!r}')


def compile_glob(pattern, location):
    # Same case-sensitive POSIX language as FileMapGlob, including literal [].
    validate_pattern(pattern, location)
    expression, index = [], 0
    while index < len(pattern):
        if pattern[index:index + 3] == '**/':
            expression.append('(?:.*/)?')
            index += 3
        elif pattern[index:index + 2] == '**':
            expression.append('.*')
            index += 2
        else:
            expression.append('[^/]*' if pattern[index] == '*' else re.escape(pattern[index]))
            index += 1
    return re.compile(''.join(expression), re.ASCII)


def patterns(value, location):
    if not isinstance(value, list) or any(not isinstance(p, str) for p in value):
        fail(location, 'expected a list of patterns')
    return [compile_glob(p, location) for p in value]


def path_set(value, location):
    fields(value, ('include', 'exclude'), location)
    if not isinstance(value['include'], list):
        fail(location, 'include must be a list')
    for item in value['include']:
        fields(item, ('pattern', 'optional'), location)
        compile_glob(item['pattern'], location)
        if type(item['optional']) is not bool:
            fail(location, f"{item['pattern']}: optional must be a boolean")
    patterns(value['exclude'], location)


def unique_object(items):
    result = {}
    for key, value in items:
        if key in result:
            fail(key, 'duplicate JSON field')
        result[key] = value
    return result


class Selection:
    def __init__(self, repository):
        self.root = Path(repository).resolve()
        self._expanded = {}
        self.safe_file(MANIFEST)
        try:
            self.data = json.loads((self.root / MANIFEST).read_text(encoding='utf-8'),
                                   object_pairs_hook=unique_object)
        except (OSError, UnicodeError, ValueError) as error:
            fail('declaration', str(error))
        keys = {'schema_version', 'report_modules', 'inspector_sources',
                'config_inputs', 'producer_scopes'}
        if 'dependency_sources' in self.data:
            keys.add('dependency_sources')
        if 'report_execution' in self.data:
            keys.add('report_execution')
        fields(self.data, keys, 'declaration')
        if type(self.data['schema_version']) is not int or self.data['schema_version'] != 1:
            fail('schema_version', 'unsupported version')
        for name in ('report_modules', 'inspector_sources', 'config_inputs'):
            path_set(self.data[name], name)
        if 'dependency_sources' in self.data:
            path_set(self.data['dependency_sources'], 'dependency_sources')
        fields(self.data['producer_scopes'], SCOPES, 'producer_scopes')
        for scope, value in self.data['producer_scopes'].items():
            path_set(value, 'producer_scopes.' + scope)
        if 'report_execution' in self.data:
            execution = self.data['report_execution']
            fields(execution, (*REPORT_EXECUTION, 'toolchain'), 'report_execution')
            if execution['toolchain'] != 'lean-toolchain':
                fail('report_execution.toolchain', 'requires the registered lean-toolchain pin')
            if dict(pattern='lean-toolchain', optional=False) not in self.data['config_inputs']['include']:
                fail('config_inputs', 'execution toolchain must be a required registered input')
            if 'lean-toolchain' not in self.expand('config_inputs'):
                fail('config_inputs', 'execution toolchain cannot be excluded')
            for field, supported in REPORT_EXECUTION.items():
                value = execution[field]
                if (not isinstance(value, list) or any(not isinstance(item, str) for item in value)
                        or len(value) != len(supported) or set(value) != set(supported)):
                    fail('report_execution.' + field, f'requires the explicit supported set {list(supported)}')
        # These required inputs keep policy and reader in the provenance/scope inventory.
        required = self.data['producer_scopes']['lean-report']['include']
        for anchor in (MANIFEST, LOADER):
            if dict(pattern=anchor, optional=False) not in required:
                fail('producer_scopes.lean-report', f'missing required registration {anchor}')
        self.modules()

    def compatibility(self):
        return hashlib.sha256(
            f"schema={REPORT_FORMAT}\n".encode('ascii')
        ).hexdigest()

    def safe_file(self, relative):
        validate_pattern(relative, 'path')
        path = self.root
        for part in relative.split('/'):
            path = path / part
            if path.is_symlink():
                fail(relative, 'registered input must not traverse a symlink')
        if not path.is_file():
            fail(relative, 'required registered file is absent or not a regular file')
        return path

    def expand(self, name):
        if name in self._expanded:
            return self._expanded[name]
        value = (self.data['producer_scopes'][name] if name in SCOPES else self.data[name])
        excluded = patterns(value['exclude'], name + '.exclude')
        result = {}
        for item in value['include']:
            pattern = item['pattern']
            matcher = compile_glob(pattern, name)
            if '*' not in pattern:
                matches = [pattern] if (self.root / pattern).exists() or (self.root / pattern).is_symlink() else []
            else:
                # Walk only the literal prefix of this registered glob. Nothing
                # outside these prefixes can enter the selected population.
                prefix = pattern.split('*', 1)[0].rsplit('/', 1)[0] if '/' in pattern.split('*', 1)[0] else ''
                start = self.root / prefix
                if start.is_symlink():
                    fail(name, f'{pattern}: registered glob root is a symlink')
                matches = []
                def traversal_error(error):
                    if isinstance(error, FileNotFoundError):
                        return
                    detail = error.strerror or str(error)
                    fail(name, f'{pattern}: registered source traversal failed: {detail}')

                for directory, dirs, files in os.walk(start, onerror=traversal_error,
                                                      followlinks=False):
                    # Excluded build trees need not be traversed.
                    dirs[:] = [d for d in dirs if not any(
                        e.fullmatch((Path(directory) / d).relative_to(self.root).as_posix() + '/')
                        for e in excluded)]
                    for filename in files:
                        path = (Path(directory) / filename).relative_to(self.root).as_posix()
                        if matcher.fullmatch(path):
                            matches.append(path)
            matches = sorted(p for p in matches if not any(e.fullmatch(p) for e in excluded))
            if not matches and not item['optional']:
                fail(name, f'{pattern}: required registration has no files after exclusions')
            for path in matches:
                self.safe_file(path)
                result[path] = None
        self._expanded[name] = list(result)
        return self._expanded[name]

    def modules(self):
        result = {}
        for path in self.expand('report_modules'):
            if not path.endswith('.lean'):
                fail(path, 'report_modules must select Lean source files')
            name = path[:-5].replace('/', '.')
            if name in result:
                fail(path, f'conflicting module name {name}')
            result[name] = path
        return result

    def producer_paths(self, scope):
        if scope not in SCOPES:
            fail(scope, 'unknown producer scope')
        selected = self.expand('lean-report') + self.expand('inspector_sources')
        if scope == 'scribe-content':
            selected += self.expand('scribe-content')
        return sorted(set(selected))

    def dependency_sources(self):
        """Permitted local compiler inputs, not a regeneration fingerprint.

        Lake selects the actual closure separately for each reported module.
        Producer-only files in this inventory do not invalidate reports.
        """
        paths = sorted(set(self.expand('report_modules') +
            (self.expand('dependency_sources') if 'dependency_sources' in self.data else [])))
        for path in paths:
            if not path.endswith('.lean'):
                fail(path, 'dependency_sources must select Lean source files')
        return paths

    def validate(self, scope):
        self.producer_paths(scope)
        self.expand('config_inputs')
        self.dependency_sources()

    def projection(self, scope):
        if scope not in SCOPES:
            fail(scope, 'unknown producer scope')
        value = dict(self.data)
        value['producer_scopes'] = {name: self.data['producer_scopes'][name]
            for name in (SCOPES if scope == 'scribe-content' else ('lean-report',))}
        return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True) + '\n'

    def scribe_affected(self, changed_paths):
        # Match declarations, including deleted optional/growth-glob members.
        # A missing required member still fails validation before this query.
        values = [self.data['producer_scopes'][scope] for scope in SCOPES]
        values.append(self.data['inspector_sources'])
        return any(any(compile_glob(p['pattern'], 'scribe-content').fullmatch(path)
                       for p in value['include'])
                   and not any(e.fullmatch(path) for e in patterns(value['exclude'], 'scribe-content'))
                   for path in changed_paths for value in values)



# The optional Git-blob memo has the same eligibility and on-disk format as
# the shell entry. Keep hashing in the consumer process instead of starting
# interpreters for each manifest, memo and coordinate operation.
def coordinate_hashes(producer, resident, sources, config):
    if any(not re.fullmatch(r'[0-9a-f]{64}', value)
           for value in (producer, resident, sources, config)):
        raise ValueError('coordinates require producer, resident, sources, config SHA-256')
    common = (f'repository_inspector_sha256={resident}\n'
              f'lean_sources_sha256={sources}\nlean_config_sha256={config}\n')
    pair = 'schema=stratalint-lean-report-input-v1\n' + f'producer_sha256={producer}\n' + common
    repository = 'schema=stratalint-lean-report-repository-input-v1\n' + common
    return (hashlib.sha256(pair.encode('ascii')).hexdigest(),
            hashlib.sha256(repository.encode('ascii')).hexdigest())


def _memo_trusted(root):
    info = root.stat()
    return root.is_dir() and info.st_uid == os.getuid() and not info.st_mode & 0o022


def _read_memo(path):
    memo = {}
    if path.exists():
        with path.open('r', encoding='ascii', newline='') as source:
            for line in source:
                fields = line[:-1].split(' ')
                if (not line.endswith('\n') or len(fields) != 2
                        or not re.fullmatch(r'(?:[0-9a-f]{40}|[0-9a-f]{64})', fields[0])
                        or not re.fullmatch(r'[0-9a-f]{64}', fields[1]) or fields[0] in memo):
                    raise ValueError('malformed memo')
                memo[fields[0]] = fields[1]
    return memo


def _prepare_memo(repository, root):
    if root is None:
        return {}, {}, False
    try:
        status = subprocess.check_output(['git', '-C', str(repository), 'status',
            '--porcelain=v1', '-z', '--untracked-files=all'], stderr=subprocess.DEVNULL)
        index = subprocess.check_output(['git', '-C', str(repository), 'ls-files',
            '-s', '-z'], stderr=subprocess.DEVNULL)
        root.mkdir(parents=True, mode=0o700, exist_ok=True)
        if not _memo_trusted(root):
            return {}, {}, False
        memo_file = root / 'memo.v1'
        if memo_file.exists() and not memo_file.is_file():
            return {}, {}, False
        memo = _read_memo(memo_file)
        records = status.split(b'\0')
        dirty, position = set(), 0
        while position < len(records) and records[position]:
            record = records[position]
            position += 1
            if len(record) < 4 or record[2:3] != b' ':
                raise ValueError('malformed git status')
            dirty.add(record[3:])
            if b'R' in record[:2] or b'C' in record[:2]:
                if position >= len(records) or not records[position]:
                    raise ValueError('malformed git rename status')
                dirty.add(records[position])
                position += 1
        eligible = {}
        for record in index.split(b'\0'):
            if not record:
                continue
            header, separator, relative = record.partition(b'\t')
            fields = header.split(b' ')
            if not separator or len(fields) != 3:
                raise ValueError('malformed git index')
            mode, oid, stage = fields
            if stage == b'0' and mode in (b'100644', b'100755') and relative not in dirty:
                value = oid.decode('ascii')
                if (not re.fullmatch(r'(?:[0-9a-f]{40}|[0-9a-f]{64})', value)
                        or relative in eligible):
                    raise ValueError('malformed stage-zero git index')
                eligible[relative] = value
        return eligible, memo, True
    except (OSError, UnicodeError, ValueError, subprocess.SubprocessError):
        return {}, {}, False


def _store_memo(root, updates):
    if not updates:
        return
    temporary = None
    try:
        if not _memo_trusted(root):
            return
        memo_file = root / 'memo.v1'
        if memo_file.exists() and not memo_file.is_file():
            return
        # Merge against the latest snapshot just as the shell writer did.
        memo = _read_memo(memo_file)
        memo.update(updates)
        with tempfile.NamedTemporaryFile(mode='w', encoding='ascii', newline='',
                prefix='.memo.v1.tmp.', dir=root, delete=False) as output:
            temporary = Path(output.name)
            for oid in sorted(memo):
                output.write(f'{oid} {memo[oid]}\n')
        if _memo_trusted(root):
            os.replace(temporary, memo_file)
    except (OSError, UnicodeError, ValueError):
        pass  # This optional optimization never replaces a current input read.
    finally:
        if temporary is not None:
            try:
                temporary.unlink(missing_ok=True)
            except OSError:
                pass


def input_coordinates(repository, memo_root=None):
    inputs = Selection(repository)
    inputs.validate('lean-report')
    repository = inputs.root
    if memo_root is None:
        value = os.environ.get('STRATALINT_LEAN_INPUT_MEMO_ROOT')
        if not value:
            base = os.environ.get('XDG_CACHE_HOME')
            if base:
                value = str(Path(base) / 'stratalint-lean-input-memo')
            elif os.environ.get('HOME'):
                value = str(Path(os.environ['HOME']) / '.cache/stratalint-lean-input-memo')
        memo_root = Path(value) if value else None
    else:
        memo_root = Path(memo_root)
    eligible, memo, enabled = _prepare_memo(repository, memo_root)
    updates, digests = {}, []
    for group in ('report_modules', 'config_inputs'):
        manifest = hashlib.sha256()
        for relative in inputs.expand(group):
            path = inputs.safe_file(relative)
            oid = eligible.get(os.fsencode(relative))
            sha = memo.get(oid) if oid else None
            if sha is None:
                with open(path, 'rb') as source:
                    sha = hashlib.file_digest(source, 'sha256').hexdigest()
                if oid:
                    updates[oid] = sha
            manifest.update(sha.encode('ascii') + b'  ' + relative.encode('utf-8') + b'\n')
        digests.append(manifest.hexdigest())
    if enabled:
        _store_memo(memo_root, updates)
    producer = inputs.compatibility()
    sources, config = digests
    pair, repository_id = coordinate_hashes(producer, producer, sources, config)
    return dict(repository=repository_id, producer=producer, sources=sources, config=config, input=pair)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('validate', 'modules', 'producer-paths',
        'scribe-producer-paths', 'snapshot', 'scribe-affected', 'address', 'coordinates'))
    parser.add_argument('--repository')
    parser.add_argument('hashes', nargs='*')
    parser.add_argument('--output')
    args = parser.parse_args()
    try:
        if args.command == 'coordinates':
            if len(args.hashes) != 4:
                raise ValueError('coordinates requires four SHA-256 values')
            print(' '.join(coordinate_hashes(*args.hashes)))
            return 0
        if not args.repository or args.hashes:
            raise ValueError('--repository is required')
        if args.command == 'address':
            values = input_coordinates(args.repository)
            print(' '.join(values[key] for key in ('repository', 'producer', 'sources', 'config')))
            return 0
        selection = Selection(args.repository)
        scope = 'scribe-content' if args.command.startswith('scribe-') else 'lean-report'
        selection.validate(scope)
        if args.command == 'modules':
            print(''.join(f'{name}\t{path}\n' for name, path in selection.modules().items()), end='')
        elif args.command.endswith('producer-paths'):
            print('\n'.join(selection.producer_paths(scope)))
        elif args.command == 'scribe-affected':
            changed = sys.stdin.buffer.read().decode('utf-8').split('\0')
            print('true' if selection.scribe_affected([p for p in changed if p]) else 'false')
        elif args.command == 'snapshot':
            if not args.output:
                fail('snapshot', '--output is required')
            output = Path(args.output)
            for name, paths_value in (
                    ('sources-paths', selection.expand('report_modules')),
                    ('config-paths', selection.expand('config_inputs'))):
                (output / name).write_text(''.join(p + '\n' for p in paths_value), encoding='utf-8')
            (output / 'compatibility').write_text(selection.compatibility() + '\n', encoding='ascii')
        return 0
    except (OSError, UnicodeError, ValueError) as error:
        print(f'lean-report-selection: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
