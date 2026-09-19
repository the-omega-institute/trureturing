#!/usr/bin/env python3
"""Validate optional evidence that the complete report entry has no new work.

The registered input set, the explicitly registered execution environment and
the complete five-piece report are sealed only after defaults/report/publication
succeed. A receipt selects no rules and grants no check success. A miss returns
to the normal Lake entry; malformed authored registration remains an error.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import stat
import subprocess
import sys
import tempfile
import zipfile
import zlib

import materials
import publication

SCHEMA = 'stratalint-lean-report-reuse-v1'
SUFFIX = '.reuse.json'
COMPLETED = ['defaults', 'report', 'publication']
INVALID_SEED = (OSError, UnicodeError, ValueError, KeyError, TypeError,
                zipfile.BadZipFile, zlib.error, NotImplementedError, subprocess.CalledProcessError)
if zipfile.lzma is not None:
    INVALID_SEED += (zipfile.lzma.LZMAError,)


def capture(repository, lake):
    """Hash only the manifest's complete declared input population."""
    inputs = publication.selection.Selection(repository)
    inputs.validate('lean-report')  # Registration errors are not cache misses.
    execution = inputs.data.get('report_execution')
    if execution is None:
        return dict(eligible=False, reason='execution-not-registered')
    environment = {name: os.environ.get(name, '') for name in execution['environment']}
    # External search/sysroot paths and arbitrary option strings are not a
    # registered file population. Their presence keeps the ordinary Lake path.
    if any(environment[name] for name in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LEAN_OPTS')):
        return dict(eligible=False, reason='external-semantic-environment')
    lake = Path(lake)
    if not lake.is_absolute():
        raise ValueError('report reuse requires an absolute Lake executable')
    try:
        versions = {}
        for name in execution['tools']:
            executable = lake if name == 'lake' else lake.with_name('lean')
            version = subprocess.check_output([str(executable), '--version'],
                cwd=inputs.root, text=True, stderr=subprocess.PIPE).strip()
            if not version:
                raise ValueError('empty ' + name + ' version')
            versions[name] = version
    except (OSError, UnicodeError, ValueError, subprocess.SubprocessError) as error:
        return dict(eligible=False, reason='toolchain-unavailable', detail=str(error))
    # dependency_sources includes every report module; producer_paths includes
    # inspector/default-audit sources. Addition/deletion changes the exact map.
    paths = sorted(set(inputs.producer_paths('lean-report') + inputs.dependency_sources()
                       + inputs.expand('config_inputs')))
    files = {}
    for path in paths:
        source = inputs.safe_file(path)
        files[path] = dict(sha256=publication.digest(source), mode=stat.S_IMODE(source.stat().st_mode))
    return dict(eligible=True, files=files, compiler_input_sha256=publication.compiler_identity(str(repository)),
        execution=dict(tools=versions, platform={name: getattr(platform, name)() for name in execution['platform']},
                       environment=environment))


def bundle_hashes(report):
    publication._require_bundle_files(report)
    return {suffix: publication.digest(publication.member(report, suffix)) for suffix in publication.SUFFIXES}


def read_receipt(report, captured):
    path = publication.member(report, SUFFIX)
    if path.is_symlink() or not path.is_file():
        raise ValueError('reuse receipt is absent or nonregular')
    receipt = publication.read_json(path.read_bytes())
    materials.require_keys(receipt, {'schema', 'completed', 'inputs', 'bundle'}, 'reuse receipt')
    if receipt['schema'] != SCHEMA or receipt['completed'] != COMPLETED:
        raise ValueError('reuse receipt lacks complete entry success')
    if receipt['inputs'] != captured:
        raise ValueError('registered inputs or execution environment changed')
    if receipt['bundle'] != bundle_hashes(report):
        raise ValueError('reuse receipt bundle mismatch')
    return receipt


def miss(reason, error=None):
    result = dict(needs_lake=True, reason=reason)
    if error is not None:
        result['detail'] = str(error)
    return result


def probe(repository, report, lake):
    """Select optional downloads; only the normal entry validates publication."""
    captured = capture(repository, lake)
    if not captured['eligible']:
        return miss(captured['reason'])
    try:
        read_receipt(report, captured)
    except INVALID_SEED as error:
        return miss('seed-rejected', error)
    return dict(needs_lake=False, reason='receipt-matched')


def write_receipt(report, captured):
    path = publication.member(report, SUFFIX)
    record = dict(schema=SCHEMA, completed=COMPLETED, inputs=captured, bundle=bundle_hashes(report))
    # Never write through cache hard links or leave a partially written receipt.
    fd, temporary = tempfile.mkstemp(prefix='.report-reuse.', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as target:
            target.write(materials.canonical_json(record))
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def seal(repository, report, lake, captured):
    current = capture(repository, lake)
    if current != captured:
        publication.member(report, SUFFIX).unlink(missing_ok=True)
        raise ValueError('registered inputs changed during report entry')
    if not captured['eligible']:
        publication.member(report, SUFFIX).unlink(missing_ok=True)
        return
    # The caller reaches this only after Lake's default+report facet and normal
    # private publication have succeeded. Bind the exact published five pieces.
    write_receipt(report, captured)


def reuse(repository, report, output, lake):
    captured = capture(repository, lake)
    if not captured['eligible']:
        return miss(captured['reason'])
    try:
        # The normal entry never trusts a prior probe. Full validation occurs
        # in publication's private snapshot, with before/after material hashes.
        receipt = read_receipt(report, captured)
        coordinates = publication.coordinates(repository)
        publication.publish(report, output, coordinates, repository, mode='cached',
                            expected_hashes=receipt['bundle'])
        # Rebind source evidence after publication; a same-path republish may
        # only change publication mode, not the report or its material bytes.
        if Path(report).resolve() != Path(output).resolve():
            if receipt != read_receipt(report, captured):
                raise ValueError('reuse receipt changed during publication')
        if capture(repository, lake) != captured:
            raise ValueError('registered inputs changed during reuse')
        write_receipt(output, captured)
    except INVALID_SEED as error:
        publication.member(output, SUFFIX).unlink(missing_ok=True)
        return miss('seed-rejected', error)
    return dict(needs_lake=False, reason='complete-entry-reused')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('probe', 'reuse', 'capture', 'seal'))
    parser.add_argument('--repository', required=True, type=Path)
    parser.add_argument('--lake', required=True, type=Path)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--snapshot', type=Path)
    args = parser.parse_args()
    if args.command in ('probe', 'reuse', 'seal') and args.report is None:
        parser.error('--report is required')
    if args.command == 'reuse' and args.output is None:
        parser.error('--output is required')
    if args.command in ('capture', 'seal') and args.snapshot is None:
        parser.error('--snapshot is required')
    if args.command == 'capture':
        args.snapshot.write_bytes(materials.canonical_json(capture(args.repository, args.lake)))
    elif args.command == 'seal':
        seal(args.repository, args.report, args.lake, publication.read_json(args.snapshot.read_bytes()))
    elif args.command == 'probe':
        print(json.dumps(probe(args.repository, args.report, args.lake), separators=(',', ':')))
    else:
        result = reuse(args.repository, args.report, args.output, args.lake)
        print('LEAN_INSPECTOR_REUSE ' + json.dumps(result, separators=(',', ':')))
        if result['needs_lake']:
            return 3
        print('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0')
        print(f'RAW_LEAN_REPORT path={args.output} sha256={publication.digest(args.output)}')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except INVALID_SEED as error:
        print(f'lean-inspector-reuse: {error}', file=sys.stderr)
        raise SystemExit(1)
