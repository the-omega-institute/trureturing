#!/usr/bin/env python3
"""Compare stock/patched identities on supplied immutable Lean source inputs.

Inputs are read-only committed source copies, not another checkout. Output is an
ordinary native Inspector publication plus measured declaration classifications.
The normal Lake graph builds real pinned Mathlib plugins and module dependencies.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import unittest

from test_native_support import NativeTestSupport, ROOT, publication, materials


class ScopeFixture(NativeTestSupport, unittest.TestCase):
    pass


def measure_scope(sources=None):
    """Pinned import closure for supplied sources or complete default libraries."""
    candidates = {p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.'): p
                  for p in (ROOT / 'D5').rglob('*.lean')}
    candidates['Trureturing'] = ROOT / 'Trureturing.lean'
    audit = ROOT / 'tools/lean-inspector'
    for p in (audit / 'LeanInformationAudit').rglob('*.lean'):
        candidates[p.relative_to(audit).with_suffix('').as_posix().replace('/', '.')] = p
    if (audit / 'LeanInformationAudit.lean').is_file():
        candidates['LeanInformationAudit'] = audit / 'LeanInformationAudit.lean'
    roots = set(candidates)
    if sources is not None:
        supplied = {p.relative_to(sources).with_suffix('').as_posix().replace('/', '.'): p
                    for p in sources.rglob('*.lean')}
        candidates.update(supplied)
        roots = set(supplied)
    for package in (ROOT / '.lake/packages').iterdir():
        for p in package.rglob('*.lean'):
            relative = p.relative_to(package)
            if '.lake' not in relative.parts:
                candidates.setdefault(relative.with_suffix('').as_posix().replace('/', '.'), p)
    names = sorted(candidates)
    pin = subprocess.check_output(['elan', 'which', 'lean'], cwd=ROOT, text=True).strip()
    read = subprocess.run([pin, '--deps-json', '--stdin'], cwd=ROOT, text=True, check=True,
        input=''.join(str(candidates[n]) + '\n' for n in names), capture_output=True, timeout=120)
    parsed = json.loads(read.stdout)['imports']
    if len(parsed) != len(names):
        raise ValueError('incomplete compiler import-graph measurement')
    errors = {name: item['errors'] for name, item in zip(names, parsed) if item['errors']}
    graph = {name: {entry['module'] for entry in item.get('result', {}).get('imports', [])}
             for name, item in zip(names, parsed)}
    closure = set(roots)
    while True:
        enlarged = closure | {dep for n in closure for dep in graph.get(n, ()) if dep in candidates}
        if enlarged == closure:
            break
        closure = enlarged
    if set(errors) & closure:
        raise ValueError('errors in required source closure: ' + str({n: errors[n] for n in set(errors) & closure}))
    return dict(excluded_unreachable_parse_errors=len(errors), default_source_roots=len(roots), indexed_sources=len(candidates),
        requested_source_closure=len(closure), d5_sources=sum(n.startswith('D5.') for n in closure),
        mathlib_sources=sum(n.startswith('Mathlib.') for n in closure),
        method='pinned lean --deps-json --stdin; '
            + ('supplied source roots' if sources is not None else 'default D5 and audit library globs')
            + '; transitive source closure',
        boundary='source rebuild requirement on compiler hash change; not a whole-project timing')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--measure', action='store_true')
    parser.add_argument('--sources', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--command-timeout', type=float, default=900)
    args = parser.parse_args()
    if args.measure:
        print(json.dumps(measure_scope(args.sources)))
        return
    if args.sources is None or args.output is None:
        parser.error('--sources and --output are required')
    sources = args.sources.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    result_path = output / 'result.json'
    result_path.unlink(missing_ok=True)
    fixture = ScopeFixture()
    fixture.setUpClass()
    started = time.monotonic()
    try:
        fixture.setUp()
        fixture.ensure()  # Canonical cold-cache admission precedes Lake work.
        source_paths = sorted(sources.rglob('*.lean'))
        if not source_paths:
            raise ValueError('no committed Lean source inputs')
        paths = [p.relative_to(sources).as_posix() for p in source_paths]
        names = [p[:-5].replace('/', '.') for p in paths]
        for source, relative in zip(source_paths, paths):
            fixture.write(relative, source.read_text())
        fixture.write('utility.json', '[]')
        config = '''name = "fixture"
defaultTargets = ["Scope"]
[[require]]
name = "leanInspector"
path = "tools/lean-inspector"
[[require]]
name = "mathlib"
path = ".lake/packages/mathlib"
[[lean_lib]]
name = "Scope"
roots = ["D5"]
globs = ["D5.+"]
[[lean_lib]]
name = "LeanInformationAudit"
globs = ["LeanInformationAudit.+"]
'''
        fixture.write('lakefile.toml', config)
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        for entry in manifest['packages']:
            name = entry['name']
            directory = 'tools/lean-inspector' if name == 'leanInspector' else '.lake/packages/' + name
            if name != 'leanInspector':
                link = fixture.root / directory
                link.parent.mkdir(parents=True, exist_ok=True)
                package = ROOT / '.lake/packages' / name
                shutil.copytree(package, link, copy_function=os.link,
                    ignore=shutil.ignore_patterns('.git', '.lake', '__pycache__'))
                # Only build outputs are shared; source paths stay inside this
                # private fixture's ordinary fetched-package directory.
                if (package / '.lake').exists():
                    (link / '.lake').symlink_to(package / '.lake', target_is_directory=True)
            entry.clear()
            entry.update(type='path', scope='', name=name, manifestFile='lake-manifest.json',
                inherited=name not in ('mathlib', 'leanInspector'), dir=directory,
                configFile='lakefile.lean' if (Path(directory) if Path(directory).is_absolute() else fixture.root / directory).joinpath('lakefile.lean').exists() else 'lakefile.toml')
        manifest['name'] = 'fixture'
        fixture.write('lake-manifest.json', json.dumps(manifest))
        policy = json.loads((fixture.root / 'lean-report-inputs.json').read_text())
        policy['report_modules']['include'] = [dict(pattern=p, optional=False) for p in paths]
        policy['dependency_sources']['include'] = [dict(pattern='LeanInformationAudit/Registry.lean', optional=False)]
        fixture.write('lean-report-inputs.json', json.dumps(policy))
        checks = []
        def command(argv):
            argv = [str(a) for a in argv]
            phase_started = time.monotonic()
            print('SCOPE_COMMAND ' + json.dumps(argv), flush=True)
            completed = fixture.guarded_command(argv, timeout=args.command_timeout)
            print(completed.stdout, end='', flush=True)
            print(completed.stderr, end='', file=sys.stderr, flush=True)
            checks.append(dict(command=argv, exit=completed.returncode,
                seconds=round(time.monotonic() - phase_started, 3),
                built=sum('Built ' in line for line in (completed.stdout + completed.stderr).splitlines()),
                replayed=sum('Replayed ' in line for line in (completed.stdout + completed.stderr).splitlines())))
            print('SCOPE_COMMAND_RESULT ' + json.dumps(checks[-1]), flush=True)
            completed.check_returncode()
        # The untouched compiler supplies the independent identity baseline.
        command([fixture.lake, 'build', *names])
        recipe = fixture.root / 'tools/lean-inspector/compiler/build.py'
        inspector = ROOT / '.lake/build/lean-inspector/producer/bin/reportInspector'
        triples = []
        for source, relative in zip(source_paths, paths):
            triples += [relative[:-5].replace('/', '.'), relative, 'sha256:' + hashlib.sha256(source.read_bytes()).hexdigest()]
        baseline = output / 'baseline.json'
        spool = output / 'baseline-spool'
        command([sys.executable, '-B', recipe, 'run', 'lake', 'env', inspector,
            '--statements-only', '--output', baseline, '--material-spool', spool, *triples])
        compact = output / 'baseline-compact.json'
        materials.compact(baseline, spool, compact, fixture.root / 'lean-report-inputs.json')
        baseline.unlink()
        shutil.rmtree(spool)
        command([sys.executable, '-B', recipe, 'run', 'lake', 'build', ':report'])
        fixture.publish()
        rows = fixture.report()[0]
        old = json.loads(compact.read_text())['modules']
        def identities(modules):
            return {r['module']: (r['source_path'], r['source_sha256'],
                    [(d['name'], d['statement_id'], d['axioms'], d['include_in_statement'])
                    for d in r['declarations']]) for r in modules}
        if identities(old) != identities(rows):
            raise ValueError('compiler instrumentation changed declaration identities')
        result = dict(exit=0, modules=len(rows), declarations=sum(len(r['declarations']) for r in rows),
            generated=sum(d['generated_companion'] for r in rows for d in r['declarations']),
            declaration_identities_unchanged=True, source_and_axiom_identities_unchanged=True,
            compiler_descriptors=sorted({origin['compiler_input_sha256'] for origin in fixture.origins().values()}),
            checks=checks, seconds=round(time.monotonic() - started, 3),
            source_sha256={p: hashlib.sha256((sources / p).read_bytes()).hexdigest() for p in paths})
        for path in paths + ['lean-report-inputs.json']:
            dest = output / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(fixture.root / path, dest)
        for suffix in publication.SUFFIXES:
            shutil.copy2(publication.member(fixture.root / 'public.json', suffix),
                         publication.member(output / 'public.json', suffix))
    finally:
        if not fixture.doCleanups():
            raise RuntimeError('compiler origin scope fixture cleanup failed')
    temporary_result = result_path.with_suffix('.json.tmp')
    temporary_result.write_text(json.dumps(result, indent=2) + '\n')
    temporary_result.replace(result_path)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
