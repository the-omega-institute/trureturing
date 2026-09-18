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

MANIFEST = 'lean-report-inputs.json'
LOADER = 'tools/scripts/report/lean-report-selection.py'
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


def validate_toolchain(value):
    where = 'report_execution.toolchain'
    fields(value, ('pin', 'identities'), where)
    def text(item):
        return (isinstance(item, str) and item and item == item.strip()
                and all(32 <= ord(c) <= 126 for c in item))
    if not text(value['pin']):
        fail(where + '.pin', 'requires an explicit toolchain pin')
    identities = value['identities']
    if not isinstance(identities, list) or not identities:
        fail(where + '.identities', 'requires registered platform/tool identities')
    seen = set()
    for identity in identities:
        fields(identity, ('platform', 'tools'), where + '.identities')
        for field in ('platform', 'tools'):
            fields(identity[field], REPORT_EXECUTION[field], where + '.' + field)
            if not all(text(item) for item in identity[field].values()):
                fail(where + '.' + field, 'requires exact nonempty identity strings')
        key = tuple(identity['platform'][name] for name in REPORT_EXECUTION['platform'])
        if key in seen:
            fail(where + '.identities', 'duplicate platform identity')
        seen.add(key)


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
        keys = {'schema_version', 'report_semantic_version', 'report_modules', 'inspector_sources',
                'config_inputs', 'producer_scopes'}
        if 'dependency_sources' in self.data:
            keys.add('dependency_sources')
        if 'report_execution' in self.data:
            keys.add('report_execution')
        fields(self.data, keys, 'declaration')
        if type(self.data['schema_version']) is not int or self.data['schema_version'] != 1:
            fail('schema_version', 'unsupported version')
        if type(self.data['report_semantic_version']) is not int or self.data['report_semantic_version'] <= 0:
            fail('report_semantic_version', 'must be a positive integer')
        for name in ('report_modules', 'inspector_sources', 'config_inputs'):
            path_set(self.data[name], name)
        if 'dependency_sources' in self.data:
            path_set(self.data['dependency_sources'], 'dependency_sources')
        fields(self.data['producer_scopes'], SCOPES, 'producer_scopes')
        for scope, value in self.data['producer_scopes'].items():
            path_set(value, 'producer_scopes.' + scope)
        if 'report_execution' in self.data:
            execution = self.data['report_execution']
            fields(execution, set(REPORT_EXECUTION) | ({'toolchain'} if isinstance(execution, dict)
                and 'toolchain' in execution else set()), 'report_execution')
            for field, supported in REPORT_EXECUTION.items():
                value = execution[field]
                if (not isinstance(value, list) or any(not isinstance(item, str) for item in value)
                        or len(value) != len(supported) or set(value) != set(supported)):
                    fail('report_execution.' + field, f'requires the explicit supported set {list(supported)}')
            if 'toolchain' in execution:
                validate_toolchain(execution['toolchain'])
                if dict(pattern='lean-toolchain', optional=False) not in self.data['config_inputs']['include']:
                    fail('report_execution.toolchain', 'requires lean-toolchain as a registered config input')
        # These required inputs keep policy and reader in the provenance/scope inventory.
        required = self.data['producer_scopes']['lean-report']['include']
        for anchor in (MANIFEST, LOADER):
            if dict(pattern=anchor, optional=False) not in required:
                fail('producer_scopes.lean-report', f'missing required registration {anchor}')
        self.modules()

    def compatibility(self):
        return hashlib.sha256(
            f"schema=stratalint-lean-report-compatibility\nversion={self.data['report_semantic_version']}\n".encode('ascii')
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('validate', 'modules', 'producer-paths',
        'scribe-producer-paths', 'snapshot', 'scribe-affected'))
    parser.add_argument('--repository', required=True)
    parser.add_argument('--output')
    args = parser.parse_args()
    try:
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
