#!/usr/bin/env python3
"""Validate optional evidence that the complete report entry has no new work.

The receipt binds the complete five-piece report to Lake's per-row semantic
witness, explicit compatibility, registered coordinates and execution. Only the
current native entry can supply a witness after all semantic/export jobs succeed.
Producer program bytes are erased from data identity; required builds still run.
A download probe selects candidates, never certifies currentness or check success.
Missing historical witnesses fail closed; fallback shares Lake's prepared jobs.
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

SCHEMA = 'stratalint-lean-report-reuse-v3'
SUFFIX = '.reuse.json'
COMPLETED = ['defaults', 'report', 'publication']
INVALID_SEED = (OSError, UnicodeError, ValueError, KeyError, TypeError,
                zipfile.BadZipFile, zlib.error, NotImplementedError, subprocess.CalledProcessError)
if zipfile.lzma is not None:
    INVALID_SEED += (zipfile.lzma.LZMAError,)


class InputMismatch(ValueError):
    def __init__(self, previous, current):
        super().__init__('registered inputs or execution environment changed')
        self.mismatch = None
        if not isinstance(previous, dict) or not isinstance(previous.get('files'), dict):
            return
        old_files, new_files = previous['files'], current['files']
        old_version = previous.get('semantic_version')
        self.mismatch = dict(
            cached_semantic_version=old_version if type(old_version) is int else None,
            current_semantic_version=current['semantic_version'],
            added_inputs=len(new_files.keys() - old_files.keys()),
            removed_inputs=len(old_files.keys() - new_files.keys()),
            changed_inputs=sum(old_files[path] != new_files[path]
                               for path in old_files.keys() & new_files.keys()),
            execution_changed=previous.get('execution') != current['execution'])


def warn_mismatch(result, stream):
    """Explain an observed mismatch without changing cache acceptance or its inputs."""
    mismatch = result.get('mismatch')
    if mismatch is None:
        return
    old = mismatch['cached_semantic_version']
    new = mismatch['current_semantic_version']
    impact = ('Previous-version module reports are incompatible; a large native audit batch may be required.'
              if old is not None and old != new else
              'Lake will determine which module reports can be reused and which require regeneration.')
    message = (f"LEAN_REPORT_CACHE_MISMATCH cached_version={old if old is not None else 'unknown'} "
               f"current_version={new} added_inputs={mismatch['added_inputs']} "
               f"removed_inputs={mismatch['removed_inputs']} changed_inputs={mismatch['changed_inputs']} "
               f"execution_changed={str(mismatch['execution_changed']).lower()}. {impact} "
               'Lean compilation has independent incremental reuse. Agents: use LEAN_CACHE and LEAN_INSPECTOR_WORK '
               'to distinguish compilation from report regeneration; seed-rejected alone does not mean a full rebuild.')
    if os.environ.get('GITHUB_ACTIONS') == 'true':
        escaped = message.replace('%', '%25').replace('\r', '%0D').replace('\n', '%0A')
        print('::warning title=Lean report cache mismatch::' + escaped, file=stream, flush=True)
    else:
        print('WARNING ' + message, file=stream, flush=True)


def capture_execution(inputs):
    """The shared, explicitly admitted report execution environment."""
    execution = inputs.data.get('report_execution')
    if execution is None:
        return dict(eligible=False, reason='execution-not-registered')
    environment = {name: os.environ.get(name, '') for name in execution['environment']}
    # Elan injects the selected pin; invoking that toolchain's binary directly
    # leaves it unset. The required pin already binds both equivalent entries.
    # Preserve every distinct override without resolving or executing a tool.
    pin = inputs.safe_file(execution['toolchain']).read_text(encoding='utf-8').strip()
    if environment['ELAN_TOOLCHAIN'] == pin:
        environment['ELAN_TOOLCHAIN'] = ''
    if any(environment[name] for name in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LEAN_OPTS')):
        return dict(eligible=False, reason='external-semantic-environment')
    return dict(eligible=True, execution=dict(toolchain=execution['toolchain'], tools=execution['tools'],
        platform={name: getattr(platform, name)() for name in execution['platform']}, environment=environment))


def capture(repository):
    """Capture download coordinates; Lake owns complete semantic currentness."""
    inputs = publication.selection.Selection(repository)
    inputs.validate('lean-report')  # Registration errors are not cache misses.
    execution = capture_execution(inputs)
    if not execution['eligible']:
        return execution
    # The authored toolchain pin is the tools' registered identity. It is a
    # required config input below. Revalidating report data does not execute
    # either compiler binary or require an installed toolchain.
    # This receipt binds report data. FILEMAP's registered program targets are
    # a separate Lake build obligation enforced by inspect.sh on both hit/miss.
    # Inspector/audit implementation bytes do not invalidate report data; an
    # incompatible program change must bump the explicit semantic version.
    paths = sorted(set(inputs.expand('report_modules') + inputs.expand('config_inputs')))
    files = {}
    for path in paths:
        source = inputs.safe_file(path)
        files[path] = dict(sha256=publication.digest(source), mode=stat.S_IMODE(source.stat().st_mode))
    return dict(eligible=True, semantic_version=inputs.data['report_cache_release_semantic_version'], files=files,
        execution=execution['execution'])


def bundle_hashes(report):
    publication._require_bundle_files(report)
    return {suffix: publication.digest(publication.member(report, suffix)) for suffix in publication.SUFFIXES}


def receipt_record(data):
    """Decode the seal; callers must bind its inputs and bundle independently."""
    receipt = publication.read_json(data)
    materials.require_keys(receipt, {'schema', 'completed', 'inputs', 'bundle', 'semantic_witness'}, 'reuse receipt')
    if receipt['schema'] != SCHEMA or receipt['completed'] != COMPLETED:
        raise ValueError('reuse receipt lacks complete entry success')
    witness = receipt['semantic_witness']
    if (not isinstance(witness, dict) or set(witness) != {'schema', 'rows'}
            or witness['schema'] != 'lake-report-semantic-witness-v1'
            or not isinstance(witness['rows'], list)):
        raise ValueError('reuse receipt lacks complete Lake semantic witness')
    names = []
    for row in witness['rows']:
        if (not isinstance(row, list) or len(row) != 2 or not all(isinstance(x, str) for x in row)
                or not row[0] or len(row[1]) != 16 or any(c not in '0123456789abcdef' for c in row[1])):
            raise ValueError('invalid Lake semantic witness row')
        names.append(row[0])
    if names != sorted(set(names)):
        raise ValueError('invalid Lake semantic witness population')
    return receipt


def read_receipt(report, captured, witness=None):
    path = publication.member(report, SUFFIX)
    if path.is_symlink() or not path.is_file():
        raise ValueError('reuse receipt is absent or nonregular')
    receipt = receipt_record(path.read_bytes())
    if receipt['inputs'] != captured:
        raise InputMismatch(receipt['inputs'], captured)
    if receipt['bundle'] != bundle_hashes(report):
        raise ValueError('reuse receipt bundle mismatch')
    if witness is None:
        raise ValueError('current Lake semantic witness is required')
    if receipt['semantic_witness'] != witness:
        raise ValueError('Lake semantic witness changed')
    return receipt


def miss(reason, error=None):
    result = dict(needs_lake=True, reason=reason)
    if error is not None:
        result['detail'] = str(error)
    if isinstance(error, InputMismatch) and error.mismatch is not None:
        result['mismatch'] = error.mismatch
    return result


def probe(repository, report, witness=None):
    """Select optional downloads; only the normal entry validates publication."""
    captured = capture(repository)
    if not captured['eligible']:
        return miss(captured['reason'])
    try:
        if witness is None:
            path = publication.member(report, SUFFIX)
            if path.is_symlink() or not path.is_file():
                raise ValueError('reuse receipt is absent or nonregular')
            receipt = receipt_record(path.read_bytes())
            if receipt['inputs'] != captured:
                raise InputMismatch(receipt['inputs'], captured)
            if receipt['bundle'] != bundle_hashes(report):
                raise ValueError('reuse receipt bundle mismatch')
            return dict(needs_lake=True, reason='current-semantic-witness-required', candidate=True)
        read_receipt(report, captured, witness)
    except INVALID_SEED as error:
        return miss('seed-rejected', error)
    return dict(needs_lake=False, reason='receipt-matched')


def write_receipt(report, captured, witness):
    path = publication.member(report, SUFFIX)
    record = dict(schema=SCHEMA, completed=COMPLETED, inputs=captured, bundle=bundle_hashes(report), semantic_witness=witness)
    # Never write through cache hard links or leave a partially written receipt.
    fd, temporary = tempfile.mkstemp(prefix='.report-reuse.', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as target:
            target.write(materials.canonical_json(record))
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def seal(repository, report, captured, witness=None):
    current = capture(repository)
    if current != captured:
        publication.member(report, SUFFIX).unlink(missing_ok=True)
        raise ValueError('registered inputs changed during report entry')
    if not captured['eligible']:
        publication.member(report, SUFFIX).unlink(missing_ok=True)
        return
    # The caller reaches this only after Lake's default+report facet and normal
    # private publication have succeeded. Bind the exact published five pieces.
    if witness is None:
        raise ValueError('current Lake semantic witness is required')
    write_receipt(report, captured, witness)


def reuse(repository, report, output, witness=None):
    captured = capture(repository)
    if not captured['eligible']:
        return miss(captured['reason'])
    try:
        # The normal entry never trusts a prior probe. Full validation occurs
        # in publication's private snapshot, with before/after material hashes.
        receipt = read_receipt(report, captured, witness)
        coordinates = publication.coordinates(repository)
        publication.publish(report, output, coordinates, repository, mode='cached',
                            expected_hashes=receipt['bundle'])
        # Rebind source evidence after publication; a same-path republish may
        # only change publication mode, not the report or its material bytes.
        if Path(report).resolve() != Path(output).resolve():
            if receipt != read_receipt(report, captured, witness):
                raise ValueError('reuse receipt changed during publication')
        if capture(repository) != captured:
            raise ValueError('registered inputs changed during reuse')
        write_receipt(output, captured, witness)
    except INVALID_SEED as error:
        publication.member(output, SUFFIX).unlink(missing_ok=True)
        return miss('seed-rejected', error)
    return dict(needs_lake=False, reason='complete-entry-reused')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('probe', 'reuse', 'capture', 'seal'))
    parser.add_argument('--repository', required=True, type=Path)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--snapshot', type=Path)
    parser.add_argument('--witness', type=Path)
    parser.add_argument('--diagnostics', action='store_true',
                        help='emit probe mismatch warnings to stderr while retaining JSON stdout')
    args = parser.parse_args()
    if args.command in ('probe', 'reuse', 'seal') and args.report is None:
        parser.error('--report is required')
    if args.command == 'reuse' and args.output is None:
        parser.error('--output is required')
    if args.command in ('capture', 'seal') and args.snapshot is None:
        parser.error('--snapshot is required')
    witness = publication.read_json(args.witness.read_bytes()) if args.witness else None
    if args.command == 'capture':
        args.snapshot.write_bytes(materials.canonical_json(capture(args.repository)))
    elif args.command == 'seal':
        seal(args.repository, args.report, publication.read_json(args.snapshot.read_bytes()), witness)
    elif args.command == 'probe':
        result = probe(args.repository, args.report, witness)
        print(json.dumps(result, separators=(',', ':')))
        if args.diagnostics:
            warn_mismatch(result, sys.stderr)
    else:
        result = reuse(args.repository, args.report, args.output, witness)
        print('LEAN_INSPECTOR_REUSE ' + json.dumps(result, separators=(',', ':')))
        warn_mismatch(result, sys.stdout)
        if result['needs_lake']:
            return 3
        print('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0')
        print(f'RAW_LEAN_REPORT path={args.output} sha256={publication.digest(args.output)}')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except publication.PublicationFailure as error:
        print(f'lean-inspector-publication: {error}', file=sys.stderr)
        raise SystemExit(2)
    except INVALID_SEED as error:
        print(f'lean-inspector-reuse: {error}', file=sys.stderr)
        raise SystemExit(1)
