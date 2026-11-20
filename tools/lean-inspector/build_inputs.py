"""Explicit compilation and regression checks for consumers that request a built report."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

import build_work
import publication
import reuse

ROOT = Path(__file__).resolve().parents[2]
PRODUCER = ROOT / 'tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll'
TOOLS = ['leanInspector/inputDiscovery', 'leanInspector/reportInspector']


def selected_programs():
    defaults = ['leanInspector/LeanInformationAudit', 'leanInspector/reportInspector',
                'leanInspectorInterface/LeanInformationAuditInterface', 'reg/Reg']
    targets = json.loads(os.environ.get('STRATALINT_LEAN_BUILD_TARGETS', json.dumps(defaults)))
    if not isinstance(targets, list) or any(not isinstance(item, str) or not re.fullmatch(
            r'[A-Za-z][A-Za-z0-9_.]*(/[A-Za-z][A-Za-z0-9_.]*)?', item) for item in targets):
        raise ValueError('invalid preparation targets')
    return targets


def prepare(roots, directory, need_inputs=True):
    if not roots and os.environ.get('FULL_BUILD') != '1':
        raise ValueError('full report preparation requires FULL_BUILD=1 or explicit LEAN_TARGETS')
    programs = [] if roots else selected_programs()
    if not need_inputs and not programs:
        return
    producer = os.environ.get('STRATALINT_LEAN_PRODUCER_DLL')
    if not producer:
        subprocess.run(['dotnet', 'build', 'tools/StrataLint.Lean/StrataLint.Lean.csproj',
                        '-c', 'Release', '--nologo'], cwd=ROOT, check=True)
        producer = str(PRODUCER)
    if not Path(producer).is_absolute() or not Path(producer).is_file():
        raise ValueError('missing prebuilt Lean producer DLL: ' + producer)
    os.environ['STRATALINT_LEAN_PRODUCER_DLL'] = producer
    if roots:
        subprocess.run(['make', 'lean', 'LEAN_TARGETS=' + ' '.join(TOOLS)], cwd=ROOT, check=True)
        scope = subprocess.check_output([sys.executable, '-B', 'tools/lean-inspector/scoped.py',
            'targets', '--repository', str(ROOT), '--targets', roots], cwd=ROOT, text=True)
        targets = scope.split()
        if not targets:
            raise ValueError('scope discovery returned no compilation targets')
    else:
        targets = programs
        if need_inputs:
            targets = [*targets, *TOOLS, 'regInspector/auricFibAnalysis']
    commands = [['make', 'lean', 'LEAN_TARGETS=' + ' '.join(sorted(set(targets)))]]
    if not roots and need_inputs:
        modules = publication.selection.Selection(ROOT).modules()
        reported_paths = set(modules.values())
        utilities = json.loads(subprocess.check_output(['dotnet', producer, 'lean-utility-input'], cwd=ROOT))
        required = {entry['claimModule'] for entry in utilities if entry['modulePath'] in reported_paths}
        # Selected registrations refer to the registry through the compiler environment.
        required.add('LeanInformationAudit.TemplateEnrollment')
        manifest = directory / 'compile-modules.json'
        manifest.write_text(json.dumps(sorted(required | modules.keys())))
        commands.append(['bash', 'tools/scripts/worktree/lean-cache-run.sh',
                         '--build-report-modules', str(manifest)])
    out = directory / 'programs.stdout.log'
    err = directory / 'programs.stderr.log'
    with out.open('w') as stdout, err.open('w') as stderr:
        for command in commands:
            result = subprocess.run(command, cwd=ROOT, stdout=stdout, stderr=stderr)
            if result.returncode:
                break
    (directory / 'programs.exit.log').write_text(str(result.returncode) + '\n')
    if result.returncode:
        for path in (out, err):
            with path.open() as stream:
                for line in stream:
                    print(line, end='', file=sys.stderr)
        result.check_returncode()


def checked_report(directory, output, seed, program_logs, work_file, *, try_seed):
    captured = reuse.capture(ROOT)
    candidate = directory / publication.RAW
    logs = Path(os.environ.get('STRATALINT_LEAN_REPORT_LOG_DIR', str(output) + '.logs')).resolve()
    reused = False
    seed_commit = None
    if try_seed:
        with reuse.publication_guard(ROOT, seed):
            if seed == reuse.canonical_seed(ROOT):
                seed_commit = reuse.read_seed_base(ROOT)
            reused = (captured.get('covers_compiler_dependencies', False)
                      and not reuse._reuse(ROOT, seed, candidate)['needs_lake'])
        if not reused:
            # Seed bytes changed since resource planning. Prepare the compiler inputs for extraction.
            prepare('', program_logs)
    if not reused:
        env = dict(os.environ, STRATALINT_LEAN_REPORT_LOG_DIR=str(logs),
                   STRATALINT_LEAN_BUILD_WORK_FILE=str(directory / 'analysis-work.json'))
        subprocess.run(['make', 'lean-report', 'LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build',
                        'LEAN_REPORT=' + str(candidate)], cwd=ROOT, env=env, check=True)
    # Keep stable comparison data across regressions that build transient Lean fixtures.
    previous = directory / 'previous' / publication.RAW
    previous.parent.mkdir()
    observed_members = ('', '.provenance.json', reuse.SUFFIX)
    with reuse.publication_guard(ROOT, output):
        try:
            checked_previous = reuse.read_receipt(output)['completed'] == reuse.CHECKED
        except reuse.INVALID_SEED:
            checked_previous = False
        for suffix in observed_members:
            path = publication.member(output, suffix)
            if path.exists():
                os.link(path, publication.member(previous, suffix))
    selected = os.environ.get('STRATALINT_FIB_REGRESSIONS_SELECTED', 'false')
    if selected not in ('true', 'false'):
        raise ValueError('invalid FIB regression selection')
    same = (checked_previous and reused and seed == output and previous.exists()
            and publication.digest(previous) == publication.digest(candidate))
    if not same or selected == 'true':
        subprocess.run([sys.executable, '-B', 'tools/lean-inspector/fib_analysis.py', str(candidate),
                        '--regressions', str(ROOT), '--previous', str(previous),
                        '--selected', selected, *([] if checked_previous else ['--unverified-previous'])], cwd=ROOT, check=True)
    else:
        print('LEAN_INSPECTOR_FIB_REGRESSIONS changed=false selected=false', flush=True)
    with reuse.publication_guard(ROOT, output):
        for suffix in observed_members:
            observed = publication.member(previous, suffix)
            current = publication.member(output, suffix)
            if observed.exists() != current.exists() or observed.exists() and not observed.samefile(current):
                raise ValueError('published report changed during regression check')
        if reuse.capture(ROOT) != captured:
            raise ValueError('inputs changed during report check')
        identity = publication.publish(candidate, output, publication.coordinates(ROOT), ROOT, validate=False)
        publication.member(output, reuse.SUFFIX).unlink(missing_ok=True)
        reuse._seal(ROOT, output, captured, identity, checked=True, reused=reused, seed_commit=seed_commit)
    try:
        logs.mkdir(parents=True, exist_ok=True)
        for path in program_logs.glob('programs.*.log'):
            shutil.copyfile(path, logs / path.name)
        phases = [] if reused else ['report']
        if (program_logs / 'programs.exit.log').exists():
            phases.append('programs')
        build_work.record(ROOT, logs, work_file, *phases)
    except (OSError, ValueError, TypeError, KeyError) as error:
        print('LEAN_BUILD_WORK_UNKNOWN ' + str(error), file=sys.stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['prepare', 'check'])
    parser.add_argument('--targets', default='')
    parser.add_argument('--output', type=Path, default=reuse.canonical_seed(ROOT))
    args = parser.parse_args()
    if args.action == 'check' and (args.targets or os.environ.get('FULL_BUILD') != '1'):
        raise ValueError('checking the full report requires FULL_BUILD=1')
    work_file = Path(os.environ.get('STRATALINT_LEAN_BUILD_WORK_FILE', ROOT / 'build/lean-cache/build-work.json'))
    if args.action == 'check':
        work_file.unlink(missing_ok=True)
    output = args.output.resolve()
    seed = Path(os.environ.get('STRATALINT_LEAN_REPORT_REUSE', output)).resolve()
    force = (os.environ.get('REBUILD_REPORT_CACHE') == '1'
             or os.environ.get('REGENERATE_REPORT_ARTIFACTS') == '1')
    if args.action == 'check' and not force and os.environ.get('LEAN_REPORT_CACHE_MISS_POLICY') == 'fetch-or-fail':
        with reuse.compatible_seed(ROOT, seed) as compatible:
            seed = compatible
    need_inputs = (args.action == 'prepare' or force
                   or reuse.probe(ROOT, seed, require_covered_dependencies=True)['needs_lake'])
    with tempfile.TemporaryDirectory(prefix='lean-programs.') as logs:
        program_logs = Path(logs)
        prepare(args.targets, program_logs, need_inputs)
        if args.action == 'check':
            # Stage next to the destination so comparison snapshots can use hard links.
            output.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory(prefix='.lean-report-build.', dir=output.parent) as staging:
                checked_report(Path(staging), output, seed, program_logs, work_file, try_seed=not need_inputs)


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode if error.returncode > 0 else 128 - error.returncode)
    except (OSError, ValueError) as error:
        print('lean-report build: ' + str(error), file=sys.stderr)
        sys.exit(2)
