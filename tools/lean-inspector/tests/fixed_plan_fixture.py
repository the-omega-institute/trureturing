"""Real fixed-template plans across a warm semantic-policy transition.

The private fixture uses ordinary Lake compilation and the normal Inspector.
Only the registered manifest changes between prior and current builds.
"""
import json
import os
from pathlib import Path
import shutil
import sys

from test_native_support import NativeTestSupport, ROOT, materials, publication

OWNER = 'LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.BindingOwner'
PATH = 'tools/lean-inspector/' + OWNER.replace('.', '/') + '.lean'


def stamps(root):
    return {p.relative_to(root).as_posix(): [p.stat().st_mtime_ns, publication.digest(p)]
            for p in (root / '.lake').rglob('*.olean')}


def main(operation, destination):
    destination = Path(destination).resolve()
    destination.mkdir(parents=True, exist_ok=True)
    private = destination / 'repository'
    runner = NativeTestSupport()
    runner.root, runner.env = destination, dict(os.environ)
    checks_path = destination / 'checks.json'
    checks = json.loads(checks_path.read_text()) if checks_path.exists() else []

    def command(args, cwd=private):
        import time
        start = time.monotonic()
        result = runner.guarded_command([str(a) for a in args], cwd=cwd, timeout=120)
        checks.append(dict(operation=operation, command=[str(a) for a in args],
            exit=result.returncode, seconds=round(time.monotonic() - start, 3),
            built=sum('Built ' in line for line in (result.stdout + result.stderr).splitlines())))
        checks_path.write_text(json.dumps(checks, indent=2) + '\n')
        print(json.dumps(checks[-1]), flush=True)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        return result

    recipe = ROOT / 'tools/lean-inspector/compiler/build.py'
    if operation == 'prepare':
        command(['make', 'lean', 'LEAN_TARGETS=' + OWNER + ' leanInspector/reportInspector'], cwd=ROOT)
    elif operation == 'snapshot':
        private.mkdir()
        for name in ['D5', 'tools/lean-inspector']:
            shutil.copytree(ROOT / name, private / name,
                ignore=shutil.ignore_patterns('.lake', '__pycache__'))
        for name in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lean-report-inputs.json']:
            shutil.copy2(ROOT / name, private / name)
        # Preserve the producer's original traces together with its artifacts.
        # Lake cache restoration creates synthetic traces, which deliberately
        # cannot certify a retained fixed-template plan's input closure.
        copy = ['cp', '-cR'] if sys.platform == 'darwin' else ['cp', '-a', '--reflink=auto']
        command([*copy, ROOT / '.lake', private / '.lake'])
        policy = json.loads((private / 'lean-report-inputs.json').read_text())
        policy['report_semantic_version'] -= 1
        (private / 'lean-report-inputs.json').write_text(json.dumps(policy, indent=2) + '\n')
    elif operation in ('prior-build', 'current-build', 'reuse-build'):
        if operation == 'current-build':
            shutil.copyfile(ROOT / 'lean-report-inputs.json', private / 'lean-report-inputs.json')
        before = stamps(private)
        built = command([sys.executable, '-B', recipe, 'run', 'lake', 'build',
            OWNER, 'leanInspector/reportInspector'])
        after = stamps(private)
        changed = sorted(p for p in after if before.get(p) != after[p])
        if operation == 'current-build':
            # These are the two plan owners in this fixture's actual closure.
            expected = ['LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates', OWNER]
            expected = {'.lake/build/lib/lean/' + n.replace('.', '/') + '.olean' for n in expected}
            if set(changed) != expected:
                raise AssertionError('incorrect affected compilation scope: ' + repr(changed))
            setup = json.loads((private / '.lake/build/ir' / (OWNER.replace('.', '/') + '.setup.json')).read_text())
            requested = {'.lake/build/lib/lean/' + OWNER.replace('.', '/') + '.olean'}
            for arts in setup['importArts'].values():
                for path in arts[0]:
                    if path.endswith('.olean') and '/.lake/' in path:
                        requested.add('.lake/' + path.split('/.lake/', 1)[1])
            if not requested.issubset(after):
                raise AssertionError('Lake setup references an absent compiled dependency')
            (destination / 'affected.json').write_text(json.dumps(dict(compiled=changed,
                requested_olean_count=len(requested), requested_oleans_reused=len(requested) - len(changed),
                cached_oleans_unchanged=len(after) - len(changed)), indent=2) + '\n')
        if operation == 'reuse-build' and (changed or 'Built ' in built.stdout + built.stderr):
            raise AssertionError('unchanged input recompiled modules: ' + repr(changed))
    elif operation in ('prior-report', 'stale-report', 'current-report', 'reuse-report'):
        label = operation.split('-')[0]
        if label == 'stale':
            shutil.copyfile(ROOT / 'lean-report-inputs.json', private / 'lean-report-inputs.json')
        output, spool = destination / (label + '.spool.json'), destination / (label + '.spool')
        inspector = private / '.lake/build/lean-inspector/producer/bin/reportInspector'
        command([sys.executable, '-B', recipe, 'run', 'lake', 'env', inspector,
            '--output', output, '--material-spool', spool, OWNER, PATH,
            'sha256:' + publication.digest(private / PATH)])
        compact = destination / (label + '.json')
        materials.compact(output, spool, compact, private / 'lean-report-inputs.json')
        rows = publication.validate_rows(compact, publication.member(compact, '.materials.zip'),
            manifest=private / 'lean-report-inputs.json')
        records = rows[0]['information_templates']['records']
        if label == 'stale':
            if not records or any(r['state'] != 'declared_unresolved' or
                    'E7.stale_source' not in json.dumps(r['diagnostic']) or
                    'lean-report-inputs.json' not in json.dumps(r['diagnostic']) for r in records):
                raise AssertionError('stale compiled plan escaped fail-closed assessment: ' + repr(records))
            return
        if not records or any(r['state'] != 'declared_validated' for r in records):
            raise AssertionError('stale normal fixed-template plan: ' + repr(records))
        def identities(data):
            return [(r['source_path'], r['source_sha256'],
                [(d['name'], d['statement_id'], d['axioms']) for d in r['declarations']]) for r in data]
        if label == 'current':
            if identities(rows) != identities(json.loads((destination / 'prior.json').read_text())['modules']):
                raise AssertionError('policy transition changed source/statement/axiom identities')
        if label == 'reuse':
            if compact.read_bytes() != (destination / 'current.json').read_bytes():
                raise AssertionError('unchanged rerun changed normal report bytes')
            result = dict(exit=0, source_statement_axiom_identities_unchanged=True,
                normal_records=len(records), unchanged_repeat_builds=0,
                stale_before_rebuild_rejected=any(c['operation'] == 'stale-report' and c['exit'] == 0
                    for c in checks),
                affected=json.loads((destination / 'affected.json').read_text()), checks=checks)
            (destination / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
            if retained := os.environ.get('STRATALINT_NATIVE_RESULT_DIR'):
                retained = Path(retained); retained.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(destination / 'result.json', retained / 'fixed-plan-transition.json')
            print(json.dumps(result), flush=True)
    else:
        raise ValueError('unknown fixed-plan operation: ' + operation)


if __name__ == '__main__':
    main(*sys.argv[1:])
