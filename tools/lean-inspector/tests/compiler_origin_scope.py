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


def measure_scope():
    """Pinned parser import closure for the complete declared default libraries."""
    candidates = {p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.'): p
                  for p in (ROOT / 'D5').rglob('*.lean')}
    candidates['Trureturing'] = ROOT / 'Trureturing.lean'
    audit = ROOT / 'tools/lean-inspector'
    for p in (audit / 'LeanInformationAudit').rglob('*.lean'):
        candidates[p.relative_to(audit).with_suffix('').as_posix().replace('/', '.')] = p
    if (audit / 'LeanInformationAudit.lean').is_file():
        candidates['LeanInformationAudit'] = audit / 'LeanInformationAudit.lean'
    roots = set(candidates)
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
        method='pinned lean --deps-json --stdin; default D5 and audit library globs; transitive source closure',
        boundary='source rebuild requirement on compiler hash change; not a whole-project timing')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--measure', action='store_true')
    parser.add_argument('--sources', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.measure:
        print(json.dumps(measure_scope()))
        return
    if args.sources is None or args.output is None:
        parser.error('--sources and --output are required')
    sources = args.sources.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
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
        def command(argv):
            # Keep the existing 900s scope guard and the native fixture's
            # process ownership/join contract, including timeout descendants.
            args = [str(a) for a in argv]
            process = subprocess.Popen(args, cwd=fixture.root, env=fixture.env, start_new_session=True)
            owned = (process, {})
            fixture._commands.append(owned)
            try:
                code = process.wait(timeout=900)
                if code != 0:
                    raise subprocess.CalledProcessError(code, args)
            finally:
                fixture.join_command(owned)
                fixture._commands.remove(owned)
        # The untouched compiler supplies the independent identity baseline.
        command([fixture.lake, 'build', *names])
        recipe = fixture.root / 'tools/lean-inspector/compiler/build.py'
        inspector = ROOT / '.lake/build/lean-inspector/producer/bin/reportInspector'
        triples = []
        for source, relative in zip(source_paths, paths):
            triples += [relative[:-5].replace('/', '.'), relative, 'sha256:' + hashlib.sha256(source.read_bytes()).hexdigest()]
        baseline = output / 'baseline.json'
        spool = output / 'baseline-spool'
        command([sys.executable, '-B', recipe, 'run', fixture.lake, 'env', inspector,
            '--statements-only', '--output', baseline, '--material-spool', spool, *triples])
        compact = output / 'baseline-compact.json'
        materials.compact(baseline, spool, compact, fixture.root / 'lean-report-inputs.json')
        baseline.unlink()
        shutil.rmtree(spool)
        command([sys.executable, '-B', recipe, 'run', fixture.lake, 'build', ':report'])
        fixture.publish()
        rows = fixture.report()[0]
        old = json.loads(compact.read_text())['modules']
        def identities(modules):
            return {r['module']: [(d['name'], d['statement_id'], d['axioms'], d['include_in_statement'])
                    for d in r['declarations']] for r in modules}
        if identities(old) != identities(rows):
            raise ValueError('compiler instrumentation changed declaration identities')
        result = dict(exit=0, modules=len(rows), declarations=sum(len(r['declarations']) for r in rows),
            generated=sum(d['generated_companion'] for r in rows for d in r['declarations']),
            declaration_identities_unchanged=True, seconds=round(time.monotonic() - started, 3),
            source_sha256={p: hashlib.sha256((sources / p).read_bytes()).hexdigest() for p in paths})
        for path in paths + ['lean-report-inputs.json']:
            dest = output / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(fixture.root / path, dest)
        for suffix in publication.SUFFIXES:
            shutil.copy2(publication.member(fixture.root / 'public.json', suffix),
                         publication.member(output / 'public.json', suffix))
        (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result))
    finally:
        fixture.doCleanups()


if __name__ == '__main__':
    main()
