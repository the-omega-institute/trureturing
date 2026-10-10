#!/usr/bin/env python3
"""Produce and verify explicit-root reports through Lake's existing module facets.

Lake alone decides module artifact reuse. Scoped sidecars bind a completed
report to independent roots, source inputs, configuration and execution inputs;
they are never a whole-report cache or an alternative compilation authority.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

import build_work
import materials
import native
import publication as public

SCHEMA = 'stratalint-scoped-lean-report-v1'
PROVENANCE_SCHEMA = 'stratalint-scoped-lean-report-provenance-v1'
ATTESTATION_SCHEMA = 'stratalint-scoped-lean-report-input-attestation-v1'
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def parse_targets(value):
    roots = value.split()
    if not roots or any(not MODULE.fullmatch(name) for name in roots):
        raise ValueError('scoped report requires explicit nonempty Lean module roots')
    return sorted(set(roots))


def check_destination(repository, report):
    report = Path(report)
    canonical = Path(repository) / '.lake/build/stratalint/raw-lean-report.json'
    protected = [public.member(canonical, suffix) for suffix in (*public.SUFFIXES, '.reuse.json')]
    protected.append(native.state(repository) / 'report.zip')
    for suffix in public.SUFFIXES:
        path = public.member(report, suffix)
        if any(path.resolve() == member.resolve()
                or path.exists() and member.exists() and path.samefile(member) for member in protected):
            raise ValueError('scoped output must not overwrite the canonical full report or its sidecars/receipt')
        if path.is_symlink():
            raise ValueError('scoped output must not traverse sidecar symlinks')


def check_scope(repository, scope, roots=None):
    materials.require_keys(scope, {'roots', 'modules', 'dependencies'}, 'scoped module selection')
    materials.require_sorted_strings(scope['roots'], 'scoped roots')
    if not scope['roots'] or roots is not None and scope['roots'] != roots:
        raise ValueError('scoped roots do not match the independent request')
    selection = public.selection.Selection(repository)
    registered = selection.modules()
    allowed = set(selection.dependency_sources())
    maps = []
    for kind in ('modules', 'dependencies'):
        rows = scope[kind]
        if not isinstance(rows, list) or not rows:
            raise ValueError('empty scoped membership')
        by_name, paths = {}, set()
        previous = None
        for row in rows:
            materials.require_keys(row, {'module', 'source_path', 'imports'}, 'scoped source')
            name, path = row['module'], row['source_path']
            if (not isinstance(name, str) or not MODULE.fullmatch(name)
                    or not isinstance(path, str) or path not in allowed
                    or path in paths or previous is not None and name <= previous):
                raise ValueError('invalid scoped module/source membership')
            selection.safe_file(path)
            materials.require_sorted_strings(row['imports'], 'scoped source imports for ' + name)
            if kind == 'modules' and registered.get(name) != path:
                raise ValueError('scoped source is not a registered report module')
            by_name[name] = row
            paths.add(path)
            previous = name
        maps.append(by_name)
    modules, dependencies = maps
    if (not set(scope['roots']) <= modules.keys()
            or any(dependencies.get(name) != row for name, row in modules.items())
            or set(modules) != dependencies.keys() & registered.keys()):
        raise ValueError('incomplete scoped report membership')
    return selection


def selected_utilities(scope, utilities):
    paths = {row['source_path'] for row in scope['modules']}
    return sorted((entry for entry in utilities if entry['modulePath'] in paths),
                  key=lambda entry: entry['modulePath'])


def capture(repository, scope, utilities=()):
    """Data identity for verification, never a module reuse decision."""
    inputs = check_scope(repository, scope)
    execution = inputs.data.get('report_execution')
    if execution is None:
        raise ValueError('scoped report execution inputs must be registered')
    paths = sorted({row['source_path'] for row in scope['dependencies']}
                   | set(inputs.expand('config_inputs')))
    files = {path: public.digest(inputs.safe_file(path)) for path in paths}
    return dict(schema=SCHEMA, report_format=public.selection.REPORT_FORMAT,
        scope=scope, files=files, utilities=selected_utilities(scope, utilities),
        execution=dict(toolchain=execution['toolchain'], tools=execution['tools'],
            platform={name: getattr(platform, name)() for name in execution['platform']},
            environment={name: os.environ.get(name, '') for name in execution['environment']}))


def input_sha(inputs):
    return hashlib.sha256(materials.canonical_json(inputs)).hexdigest()


def write_sidecars(report, inputs, origins):
    sha = public.digest(report)
    public.member(report, '.sha256').write_text(f'{sha}  {Path(report).name}\n', encoding='ascii')
    public.member(report, '.input.attestation').write_text(
        f'schema={ATTESTATION_SCHEMA}\ninput_sha256={input_sha(inputs)}\nreport_sha256={sha}\n', encoding='ascii')
    public.member(report, '.provenance.json').write_bytes(materials.canonical_json(dict(
        schema=PROVENANCE_SCHEMA, inputs=inputs, report_sha256=sha, module_origins=origins)))


def validate_bundle(report, repository, scope, *, utilities=(), expected=None):
    """Validate completed scoped bytes against independently discovered roots."""
    report = Path(report)
    public._require_bundle_files(report)
    sha = public.digest(report)
    if public.member(report, '.sha256').read_text(encoding='ascii') != f'{sha}  {report.name}\n':
        raise ValueError('scoped report SHA mismatch')
    provenance = public.read_json(public.member(report, '.provenance.json').read_bytes())
    materials.require_keys(provenance, {'schema', 'inputs', 'report_sha256', 'module_origins'}, 'scoped provenance')
    current = capture(repository, scope, utilities)
    if (provenance['schema'] != PROVENANCE_SCHEMA or provenance['report_sha256'] != sha
            or provenance['inputs'] != current or expected is not None and expected != current):
        raise ValueError('stale scoped input/provenance')
    attestation = (f'schema={ATTESTATION_SCHEMA}\ninput_sha256={input_sha(current)}\nreport_sha256={sha}\n')
    if public.member(report, '.input.attestation').read_text(encoding='ascii') != attestation:
        raise ValueError('invalid scoped input attestation')
    origins = provenance['module_origins']
    wanted = {row['module']: row for row in scope['modules']}
    materials.require_keys(origins, set(wanted), 'scoped production origins')
    obligations = {entry['modulePath']: entry for entry in current['utilities']}
    seen = set()
    for row in public.validated_rows(report, public.member(report, '.materials.zip'), schema=SCHEMA):
        name = row['module']
        source = wanted.get(name)
        if (source is None or row['source_path'] != source['source_path']
                or row['source_sha256'] != 'sha256:' + current['files'][source['source_path']]
                or row['imports'] != source['imports']):
            raise ValueError('scoped source/import membership mismatch')
        public.check_origin(origins[name], row)
        public.validate_template_sources([row], repository)
        obligation = obligations.get(row['source_path'])
        evidence = row.get('utility_refutation')
        if obligation is None:
            if evidence is not None:
                raise ValueError('unexpected scoped utility evidence')
        elif evidence is None or any(evidence.get(field) != obligation[raw] for raw, field in (
                ('claimGid', 'claim_gid'), ('claimSourcePath', 'claim_source_path'),
                ('claimSourceSha256', 'claim_source_sha256'), ('resultGid', 'result_gid'))):
            raise ValueError('scoped utility evidence mismatch')
        seen.add(name)
    if seen != set(wanted):
        raise ValueError('incomplete scoped report membership')


class Entry:
    def __init__(self, repository, temporary, logs):
        self.root = Path(repository).resolve()
        self.temporary, self.logs = Path(temporary), Path(logs)
        self.environment = dict(os.environ)
        self.lake = self.environment.get('LAKE_BIN') or shutil.which('lake')
        self.producer = self.environment.get('STRATALINT_LEAN_PRODUCER_DLL')

    def phase(self, name, command, *, environment=None):
        out, err = self.logs / (name + '.stdout.log'), self.logs / (name + '.stderr.log')
        print('LEAN_INSPECTOR_PHASE phase=' + name + ' status=started', file=sys.stderr, flush=True)
        with out.open('wb') as stdout, err.open('wb') as stderr:
            result = subprocess.run(command, cwd=self.root,
                env=environment or self.environment, stdout=stdout, stderr=stderr)
        (self.logs / (name + '.exit.log')).write_text(str(result.returncode) + '\n')
        if result.returncode:
            sys.stderr.write(out.read_text(errors='replace') + err.read_text(errors='replace'))
            raise subprocess.CalledProcessError(result.returncode, command)
        print('LEAN_INSPECTOR_PHASE phase=' + name + ' status=completed exit=0', file=sys.stderr, flush=True)
        return out

    def provision(self):
        if self.producer:
            if not Path(self.producer).is_absolute() or not Path(self.producer).is_file():
                raise ValueError('candidate Lean producer must be an existing absolute path')
        else:
            output = self.phase('producer-build', ['dotnet', 'build',
                str(self.root / 'tools/StrataLint.Lean/StrataLint.Lean.csproj'), '--configuration', 'Release',
                '--nologo', '--verbosity', 'quiet', '-t:Build', '-getProperty:TargetPath'])
            self.producer = output.read_text().splitlines()[-1]
            if not Path(self.producer).is_absolute() or not Path(self.producer).is_file():
                raise ValueError('producer build reported no existing absolute DLL')
        self.environment['STRATALINT_LEAN_PRODUCER_DLL'] = self.producer
        if not self.lake:
            path = self.temporary / 'toolchain-path'
            self.phase('toolchain', ['/bin/bash', str(self.root / 'tools/scripts/workflow/install-lean-toolchain.sh'),
                str(self.root / 'lean-toolchain'), '--github-path', str(path)])
            self.lake = str(Path(path.read_text().strip()) / 'lake')
        if not Path(self.lake).is_absolute() or not os.access(self.lake, os.X_OK):
            raise ValueError('an absolute executable lake path is required (LAKE_BIN)')
        self.environment['LAKE_BIN'] = self.lake
        self.phase('ensure', ['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-ensure.sh')])

    def guarded(self, *arguments):
        return ['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-run.sh'),
                self.lake, '-d', str(self.root / 'tools/lean-inspector-reg'), *arguments]

    def discover(self, roots):
        inputs = public.selection.Selection(self.root)
        inputs.validate('lean-report')
        if not set(roots) <= inputs.modules().keys():
            raise ValueError('scoped roots must be registered report modules')
        utility_file = self.phase('utility', ['dotnet', self.producer, 'lean-utility-input'])
        utilities = public.read_json(utility_file.read_bytes())
        if not isinstance(utilities, list):
            raise ValueError('utility input must be an array')
        for entry in utilities:
            materials.require_keys(entry, native.UTILITY_FIELDS, 'authoritative utility input')
            if any(not isinstance(value, str) or not value for value in entry.values()):
                raise ValueError('incomplete authoritative utility input')
        input_file = self.phase('utility-scope', ['dotnet', self.producer, 'lean-utility-input', '--scope'])
        utility_inputs = public.read_json(input_file.read_bytes())
        if not isinstance(utility_inputs, list):
            raise ValueError('utility scope input must be an array')
        for entry in utility_inputs:
            materials.require_keys(entry, {'modulePath', 'inputModules'}, 'authoritative utility scope input')
            if not isinstance(entry['modulePath'], str) or not entry['modulePath']:
                raise ValueError('incomplete authoritative utility scope input')
            materials.require_sorted_strings(entry['inputModules'], 'utility input modules')
            if any(not MODULE.fullmatch(name) for name in entry['inputModules']):
                raise ValueError('invalid utility input module')
        request, output = self.temporary / 'scope-request.json', self.temporary / 'selected-modules.json'
        request.write_bytes(materials.canonical_json(dict(roots=roots, modules=sorted(inputs.modules()),
            utilities=utilities, utility_inputs=utility_inputs)))
        self.phase('scope', self.guarded('script', 'run', 'leanInspector/reportScope', str(request), str(output)))
        scope = public.read_json(output.read_bytes())
        check_scope(self.root, scope, roots)
        self.environment['STRATALINT_INSPECTOR_SCOPE_FILE'] = str(output)
        self.environment['STRATALINT_INSPECTOR_UTILITY_INPUT'] = str(utility_file)
        return scope, utilities


def compiled_modules(root, logs):
    """Actual successful Lean build captions, separate from report extraction."""
    names = build_work.output_names(root / '.lake/build')
    result = set()
    expression = re.compile(r'^[^\s]+ \[[0-9]+/[0-9]+\](?: \(Optional\))? Built ([^\s()]+)')
    for stream in ('stdout', 'stderr'):
        for line in (logs / ('report.' + stream + '.log')).read_text().splitlines():
            if match := expression.match(line):
                target, _, facet = match[1].partition(':')
                name = target.rsplit('/', 1)[-1]
                if facet in ('', 'lean') and name in names:
                    result.add(name)
    return sorted(result)


def produce(entry, output, roots):
    scope, utilities = entry.discover(roots)
    before = capture(entry.root, scope, utilities)
    shutil.copyfile(entry.temporary / 'selected-modules.json', entry.logs / 'selected-modules.json')
    for name in ('module-work.jsonl', 'native-work.jsonl', 'native-phases.jsonl'):
        (entry.logs / name).write_text('')
    entry.environment.update(STRATALINT_INSPECTOR_MODULE_WORK=str(entry.logs / 'module-work.jsonl'),
        STRATALINT_INSPECTOR_ACTIVITY=str(entry.logs / 'native-work.jsonl'),
        STRATALINT_INSPECTOR_PHASES=str(entry.logs / 'native-phases.jsonl'))
    targets = ['+' + row['module'] + ':report' for row in scope['modules']]
    entry.phase('report', entry.guarded('build', *targets))
    if capture(entry.root, scope, utilities) != before:
        raise ValueError('scoped inputs changed during report production')
    aggregate = entry.temporary / 'scoped-report.zip'
    artifacts = [str(native.state(entry.root) / 'modules' / (row['module'] + '.zip')) for row in scope['modules']]
    native.aggregate(entry.root, aggregate, *artifacts, config=dict(
        modules=[row['module'] for row in scope['modules']], coordinates=before),
        schema=SCHEMA, write_sidecars=write_sidecars)
    report = public.unpack(aggregate, entry.temporary)
    def validator(report, expected, repository, **_):
        validate_bundle(report, repository, scope, utilities=utilities, expected=expected)
    public.publish(report, output, before, entry.root, validator=validator)
    work = [public.read_json(line) for line in (entry.logs / 'module-work.jsonl').read_text().splitlines()]
    extracted = sorted({row['module'] for row in work if row['operation'] == 'extract'})
    compiled = compiled_modules(entry.root, entry.logs)
    observation = dict(selected_modules=len(scope['modules']), extracted_modules=len(extracted),
        compiled_modules=len(compiled), extracted_module_names=extracted, compiled_module_names=compiled)
    (entry.logs / 'work.json').write_bytes(materials.canonical_json(observation))
    print('LEAN_INSPECTOR_SCOPED_WORK ' + json.dumps(observation, sort_keys=True), flush=True)
    print(f'SCOPED_LEAN_REPORT path={output} sha256={public.digest(output)}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('produce', 'verify'))
    parser.add_argument('--repository', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--targets', required=True)
    parser.add_argument('--log-dir', type=Path)
    args = parser.parse_args()
    root = args.repository.resolve()
    roots = parse_targets(args.targets)
    output = args.report if args.report.is_absolute() else root / args.report
    check_destination(root, output)
    # Input failures precede ensure, output-directory creation and any report seal.
    inputs = public.selection.Selection(root)
    inputs.validate('lean-report')
    if not set(roots) <= inputs.modules().keys():
        raise ValueError('scoped roots must be registered report modules')
    if args.command == 'verify':
        public._require_bundle_files(output)
    else:
        public.member(output, '.input.attestation').unlink(missing_ok=True)
    with tempfile.TemporaryDirectory(prefix='stratalint-scoped-report.') as directory:
        temporary = Path(directory)
        startup_logs = temporary / 'logs'
        startup_logs.mkdir()
        entry = Entry(root, temporary, startup_logs)
        entry.provision()
        if args.command == 'verify':
            scope, utilities = entry.discover(roots)
            validate_bundle(output, root, scope, utilities=utilities)
            print('SCOPED_LEAN_REPORT_VERIFIED path=' + str(output))
        else:
            logs = args.log_dir or Path(str(output) + '.logs')
            if not logs.is_absolute():
                logs = root / logs
            logs.mkdir(parents=True, exist_ok=True)
            for path in startup_logs.iterdir():
                shutil.copyfile(path, logs / path.name)
            entry.logs = logs
            produce(entry, output, roots)


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(f'lean-report-scoped: command failed with exit {error.returncode}', file=sys.stderr)
        sys.exit(error.returncode if 0 < error.returncode < 126 else 1)
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, zipfile.BadZipFile) as error:
        print(f'lean-report-scoped: {error}', file=sys.stderr)
        sys.exit(2)
