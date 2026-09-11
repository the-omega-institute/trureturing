#!/usr/bin/env python3
"""Consume the FILEMAP-registered report input and impact declaration.

Lake owns compilation. This reader only expands authored path sets and cohort
relations; report imports and typed claims are never selection authorities.
"""
import argparse
import json
import os
from pathlib import Path
import re
import sys

MANIFEST = 'lean-report-inputs.json'
LOADER = 'tools/scripts/report/lean-report-selection.py'
SCOPES = ('lean-report', 'scribe-content')


def fail(location, message):
    raise ValueError(f'{MANIFEST}: {location}: {message}')


def fields(value, expected, location):
    if not isinstance(value, dict) or set(value) != set(expected):
        actual = sorted(value) if isinstance(value, dict) else type(value).__name__
        fail(location, f'expected fields {sorted(expected)}, got {actual}')


def compile_glob(pattern, location):
    # Same case-sensitive POSIX language as FileMapGlob, including literal [].
    if (not isinstance(pattern, str) or not pattern or pattern != pattern.strip()
            or pattern.startswith('/') or '\\' in pattern or '?' in pattern
            or any(ord(c) < 32 or ord(c) > 126 for c in pattern)
            or any(p in ('', '.', '..') for p in pattern.split('/'))):
        fail(location, f'unsafe path pattern {pattern!r}')
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
        fields(self.data, ('schema_version', 'report_modules', 'inspector_sources',
                          'config_inputs', 'producer_scopes', 'impact_cohorts'), 'declaration')
        if type(self.data['schema_version']) is not int or self.data['schema_version'] != 1:
            fail('schema_version', 'unsupported version')
        for name in ('report_modules', 'inspector_sources', 'config_inputs'):
            path_set(self.data[name], name)
        fields(self.data['producer_scopes'], SCOPES, 'producer_scopes')
        for scope, value in self.data['producer_scopes'].items():
            path_set(value, 'producer_scopes.' + scope)
        # These two inputs bind policy and reader changes to compatibility.
        required = self.data['producer_scopes']['lean-report']['include']
        for anchor in (MANIFEST, LOADER):
            if dict(pattern=anchor, optional=False) not in required:
                fail('producer_scopes.lean-report', f'missing required registration {anchor}')
        cohorts = self.data['impact_cohorts']
        if not isinstance(cohorts, list) or not cohorts:
            fail('impact_cohorts', 'expected nonempty cohort list')
        self.cohorts = {}
        for cohort in cohorts:
            fields(cohort, ('id', 'members', 'exclude', 'depends_on'), 'impact_cohorts')
            name = cohort['id']
            if not isinstance(name, str) or not re.fullmatch('[A-Za-z0-9][A-Za-z0-9_-]*', name):
                fail('impact_cohorts', f'invalid id {name!r}')
            if name in self.cohorts:
                fail(name, 'duplicate cohort registration')
            if not cohort['members']:
                fail(name, 'members must be nonempty')
            members = patterns(cohort['members'], name + '.members')
            excluded = patterns(cohort['exclude'], name + '.exclude')
            dependencies = cohort['depends_on']
            if (not isinstance(dependencies, list)
                    or any(not isinstance(d, str) for d in dependencies)
                    or len(set(dependencies)) != len(dependencies)):
                fail(name, 'depends_on must be unique group IDs')
            self.cohorts[name] = (members, excluded, dependencies)
        for name, (_, _, dependencies) in self.cohorts.items():
            for dependency in dependencies:
                if dependency not in self.cohorts:
                    fail(name, f'unknown depends_on group {dependency}')
        self.modules()  # Includes exactly-one ownership for the current universe.

    def safe_file(self, relative):
        compile_glob(relative, 'path')
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

    def owner(self, path):
        universe = self.data['report_modules']
        if (not any(compile_glob(p['pattern'], 'report_modules').fullmatch(path) for p in universe['include'])
                or any(p.fullmatch(path) for p in patterns(universe['exclude'], 'report_modules.exclude'))):
            fail(path, 'current/removed path is outside report_modules registration')
        owners = [name for name, (members, excluded, _) in self.cohorts.items()
                  if any(m.fullmatch(path) for m in members) and not any(e.fullmatch(path) for e in excluded)]
        if len(owners) != 1:
            fail(path, f'expected exactly one impact_cohorts owner, got {owners}')
        return owners[0]

    def modules(self):
        result = {}
        for path in self.expand('report_modules'):
            if not path.endswith('.lean'):
                fail(path, 'report_modules must select Lean source files')
            self.owner(path)
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

    def validate(self, scope):
        self.producer_paths(scope)
        self.expand('config_inputs')

    def projection(self, scope):
        if scope not in SCOPES:
            fail(scope, 'unknown producer scope')
        value = dict(self.data)
        value['producer_scopes'] = {name: self.data['producer_scopes'][name]
            for name in (SCOPES if scope == 'scribe-content' else ('lean-report',))}
        return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True) + '\n'

    def affected(self, changed_paths, current):
        dirty = {self.owner(path) for path in changed_paths}
        reverse = {name: set() for name in self.cohorts}
        for name, (_, _, dependencies) in self.cohorts.items():
            for dependency in dependencies:
                reverse[dependency].add(name)
        pending = list(dirty)
        while pending:
            for dependent in reverse[pending.pop()]:
                if dependent not in dirty:
                    dirty.add(dependent)
                    pending.append(dependent)
        return sorted(name for name, path in current.items() if self.owner(path) in dirty)

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
                    ('producer-paths', selection.producer_paths('lean-report')),
                    ('sources-paths', list(dict.fromkeys(selection.expand('report_modules') + selection.expand('inspector_sources')))),
                    ('config-paths', selection.expand('config_inputs'))):
                (output / name).write_text(''.join(p + '\n' for p in paths_value), encoding='utf-8')
            (output / 'selection-policy.json').write_text(selection.projection('lean-report'), encoding='ascii')
        return 0
    except (OSError, UnicodeError, ValueError) as error:
        print(f'lean-report-selection: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
