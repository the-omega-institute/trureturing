#!/usr/bin/env python3
"""Measure native report jobs on a parameterized, compiler-warm Lean fixture.

The observer module must provide Sampler(library).snapshot(pid), as does the
accepted process-family counter. All tool and output paths are explicit. This
program creates only synthetic sources and retains the fixture and result data.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('source-root', 'output', 'observer-program', 'observer-library', 'lake-bin', 'dotnet-cli'):
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('--tool-path', required=True)
    parser.add_argument('--modules', type=int, default=132)
    parser.add_argument('--fixture', type=Path, help='Reuse an existing synthetic fixture, preserving its producer sources')
    args = parser.parse_args()
    if args.modules < 4:
        parser.error('--modules must be at least 4')
    source, output = args.source_root.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    fixture = args.fixture.resolve() if args.fixture else output / 'fixture'
    if fixture.exists() and not args.fixture:
        parser.error('output fixture already exists')
    os.environ['PATH'] = args.tool_path
    tests = load('native_fixture', source / 'tools/lean-inspector/tests/test_native.py')
    tests.ROOT = source
    case = tests.NativeTests()
    case.lake = str(args.lake_bin.resolve())
    case.dotnet = shutil.which('dotnet')
    case.cli = args.dotnet_cli.resolve()
    case.setUp()
    previous = str(case.root)
    if not args.fixture:
        shutil.move(case.root, fixture)
    elif not (fixture / 'lakefile.toml').read_text().startswith('name = "fixture"\n'):
        parser.error('--fixture must be a synthetic native fixture package')
    case.root = fixture
    case.env = {key: value.replace(previous, str(fixture)) for key, value in case.env.items()}
    case.env['LAKE_ARTIFACT_CACHE'] = 'false'
    case.env['STRATALINT_VALIDATION_WORK'] = str(fixture / 'validation-work.jsonl')
    if not args.fixture:
        for index in range(args.modules - 4):
            case.write(f'D5/Load{index:04}.lean',
                       f'import D5.B\ndef load{index:04} : Nat := D5.hidden + {index}\n')
    # Identical observational instrumentation in each measured source variant.
    # It counts real complete validator calls, without changing their results.
    native = fixture / 'tools/lean-inspector/native.py'
    if not args.fixture:
        native.write_text(native.read_text().replace('selection = public.selection', '''
_validate_rows = public.validate_rows
def measured_validate_rows(*args, **kwargs):
    rows = _validate_rows(*args, **kwargs)
    with open(os.environ['STRATALINT_VALIDATION_WORK'], 'a') as target:
        target.write(json.dumps(dict(modules=len(rows), declarations=sum(len(r['declarations']) for r in rows))) + '\\n')
    return rows
public.validate_rows = measured_validate_rows
selection = public.selection'''))
    if '_measured_material_identities' not in native.read_text():
        native.write_text(native.read_text().replace('selection = public.selection', '''
_measured_material_identities = materials.material_identities
def measured_material_identities(*args, **kwargs):
    result = _measured_material_identities(*args, **kwargs)
    with open(os.environ['STRATALINT_VALIDATION_WORK'], 'a') as target:
        target.write(json.dumps(dict(identities=1, modules=0, declarations=0)) + '\\n')
    return result
materials.material_identities = measured_material_identities
selection = public.selection'''))
    case.write('D5/Alone.lean', 'def alone : String := "λ😀𐀀"\nopaque concealed : Nat := 7\n')
    case.build()  # canonical ensure, defaults, producer, and real Lean fixtures
    inspector_state = fixture / '.lake/build/lean-inspector'
    for path in (inspector_state / 'modules').iterdir():
        path.unlink()
    for path in inspector_state.glob('report.zip*'):
        path.unlink()
    observer = load('native_observer', args.observer_program.resolve())
    results = dict(modules=args.modules, source_root=str(source),
                   fixture=str(fixture), source_sha256={str(path.relative_to(fixture)): hashlib.sha256(path.read_bytes()).hexdigest()
                       for path in sorted((fixture / 'tools/lean-inspector').glob('*')) if path.is_file()},
                   scope='synthetic compiler-warm fixture; sampled process-family footprint is not minimum RAM', modes={})
    for mode in ('full', 'unchanged', 'single-module'):
        if mode == 'single-module':
            case.write('D5/Alone.lean', 'def alone : String := "changed λ😀"\nopaque concealed : Nat := 7\n')
        case.write('activity.jsonl', '')
        case.write('validation-work.jsonl', '')
        sampler = observer.Sampler(args.observer_library.resolve())
        started = time.monotonic()
        samples, peak, lake_threads, lake_footprint = [], 0, 0, 0
        with (output / (mode + '.log')).open('w') as log:
            process = subprocess.Popen(['make', 'lean', 'LEAN_TARGETS=:report'], cwd=fixture,
                                       env=case.env, stdout=log, stderr=subprocess.STDOUT)
            try:
                while process.poll() is None:
                    rows, errors, host = sampler.snapshot(process.pid)
                    samples.append(dict(seconds=time.monotonic() - started, processes=rows, errors=errors, host=host))
                    peak = max(peak, sum(row['footprint_bytes'] for row in rows))
                    for row in rows:
                        if row['name'] == 'lake':
                            lake_threads = max(lake_threads, row['threads'])
                            lake_footprint = max(lake_footprint, row['footprint_bytes'])
                    try:
                        process.wait(timeout=.1)
                    except subprocess.TimeoutExpired:
                        pass
            finally:
                if process.poll() is None:
                    process.terminate()
                status = process.wait(timeout=30)
        elapsed = time.monotonic() - started
        activity = [json.loads(line) for line in (fixture / 'activity.jsonl').read_text().splitlines()]
        validation = [json.loads(line) for line in (fixture / 'validation-work.jsonl').read_text().splitlines()]
        expected = {'full': (args.modules, 1), 'unchanged': (0, 0), 'single-module': (1, 1)}[mode]
        counts = tuple(sum(row['count'] for row in activity if row['kind'] == kind) for kind in ('extract', 'aggregate'))
        results['modes'][mode] = dict(exit=status, seconds=elapsed, extraction_aggregation_counts=counts,
            lake_peak_threads=lake_threads, lake_peak_footprint_bytes=lake_footprint,
            sampled_family_peak_footprint_bytes=peak,
            material_identity_computations=sum(row.get('identities', 0) for row in validation),
            validation_calls=sum('identities' not in row for row in validation), validation_modules=sum(row['modules'] for row in validation),
            validation_declarations=sum(row['declarations'] for row in validation))
        (output / (mode + '-samples.json')).write_text(json.dumps(samples) + '\n')
        (output / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
        if status != 0 or counts != expected:
            raise RuntimeError(f'{mode}: status={status}, counts={counts}, expected={expected}; see {output}')
        # Validate with the measured producer's full validator outside timing;
        # a retained pre-change fixture can have an older sidecar contract.
        subprocess.run([sys.executable, str(native), 'validate', 'report', str(fixture),
                        str(inspector_state / 'report.zip')], env=case.env, check=True)
    print(json.dumps(results, indent=2))
    case.doCleanups()


if __name__ == '__main__':
    main()
