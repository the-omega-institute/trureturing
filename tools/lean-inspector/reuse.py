#!/usr/bin/env python3
"""Validate optional evidence that the complete report entry has no new work.

The report format, the report-module and configuration inputs, the explicitly
registered execution environment and the complete five-piece report are sealed
only after defaults/report/publication succeed. Producer program bytes are not
part of the seal; implementation changes retain historical reports. A receipt selects no rules and grants no check success. A miss returns
to the normal Lake entry under reuse-or-build. Local fetch-or-fail requires a
complete seed with the current report format before allowing that entry;
malformed authored registration remains an error.
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

SCHEMA = 'stratalint-lean-report-reuse-v4'
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
        self.mismatch = dict(
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
    impact = 'Lake determines the module work from compiler traces.'
    message = (f"LEAN_REPORT_CACHE_MISMATCH added_inputs={mismatch['added_inputs']} "
               f"removed_inputs={mismatch['removed_inputs']} changed_inputs={mismatch['changed_inputs']} "
               f"execution_changed={str(mismatch['execution_changed']).lower()}. {impact} "
               'Lean compilation has independent incremental reuse. Agents: use LEAN_CACHE and LEAN_INSPECTOR_WORK '
               'to distinguish compilation from report regeneration; seed-rejected alone does not mean a full rebuild.')
    if os.environ.get('GITHUB_ACTIONS') == 'true':
        escaped = message.replace('%', '%25').replace('\r', '%0D').replace('\n', '%0A')
        print('::warning title=Lean report cache mismatch::' + escaped, file=stream, flush=True)
    else:
        print('WARNING ' + message, file=stream, flush=True)


def capture(repository):
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
    # The authored toolchain pin is the tools' registered identity. It is a
    # required config input below. Revalidating report data does not execute
    # either compiler binary or require an installed toolchain.
    # This receipt binds report data. FILEMAP's registered program targets are
    # a separate Lake build obligation enforced by inspect.sh on both hit/miss.
    # Inspector/audit implementation bytes do not invalidate report data; an
    # implementation change retains reports; extraction changes update the format.
    paths = sorted(set(inputs.expand('report_modules') + inputs.expand('config_inputs')))
    files = {}
    for path in paths:
        source = inputs.safe_file(path)
        files[path] = dict(sha256=publication.digest(source), mode=stat.S_IMODE(source.stat().st_mode))
    return dict(eligible=True, report_format=publication.selection.REPORT_FORMAT,
        files=files,
        execution=dict(toolchain=execution['toolchain'], tools=execution['tools'],
                       platform={name: getattr(platform, name)() for name in execution['platform']},
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
        raise InputMismatch(receipt['inputs'], captured)
    if receipt['bundle'] != bundle_hashes(report):
        raise ValueError('reuse receipt bundle mismatch')
    return receipt


def miss(reason, error=None):
    result = dict(needs_lake=True, reason=reason)
    if error is not None:
        result['detail'] = str(error)
    if isinstance(error, InputMismatch) and error.mismatch is not None:
        result['mismatch'] = error.mismatch
    return result


def probe(repository, report):
    """Select optional downloads; only the normal entry validates publication."""
    captured = capture(repository)
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


def seal(repository, report, captured):
    current = capture(repository)
    if current != captured:
        publication.member(report, SUFFIX).unlink(missing_ok=True)
        raise ValueError('registered inputs changed during report entry')
    if not captured['eligible']:
        publication.member(report, SUFFIX).unlink(missing_ok=True)
        return
    # The caller reaches this only after Lake's default+report facet and normal
    # private publication have succeeded. Bind the exact published five pieces.
    write_receipt(report, captured)


def reuse(repository, report, output):
    captured = capture(repository)
    if not captured['eligible']:
        return miss(captured['reason'])
    try:
        # The receipt binds bundle bytes that were validated when produced; like
        # a restored olean they are reused as is. Publication still stages a
        # private snapshot that must match the receipt and current inputs.
        receipt = read_receipt(report, captured)
        coordinates = publication.coordinates(repository)
        publication.publish(report, output, coordinates, repository, mode='cached',
                            expected_hashes=receipt['bundle'], validate=False)
        # Rebind source evidence after publication; a same-path republish may
        # only change publication mode, not the report or its material bytes.
        if Path(report).resolve() != Path(output).resolve():
            if receipt != read_receipt(report, captured):
                raise ValueError('reuse receipt changed during publication')
        if capture(repository) != captured:
            raise ValueError('registered inputs changed during reuse')
        write_receipt(output, captured)
    except INVALID_SEED as error:
        publication.member(output, SUFFIX).unlink(missing_ok=True)
        return miss('seed-rejected', error)
    return dict(needs_lake=False, reason='complete-entry-reused')


class CacheIncompatible(ValueError):
    def __init__(self, local, restored, reason):
        super().__init__(f'LEAN_REPORT_CACHE_INCOMPATIBLE local_format={local} '
                         f'current_format={publication.selection.REPORT_FORMAT} '
                         f'restored_format={restored} reason={reason}\n'
                         'Restore with make lean-cache-from-github-without-mathlib REFRESH_STALE=1 '
                         'or rebuild explicitly with make lean-report REBUILD_REPORT_CACHE=1')


def seed_format(report):
    """Check the sealed seed without comparing current source or program bytes."""
    try:
        publication._require_bundle_files(report)
        path = publication.member(report, SUFFIX)
        if path.is_symlink() or not path.is_file():
            raise ValueError('missing reuse receipt')
        receipt = publication.read_json(path.read_bytes())
        materials.require_keys(receipt, {'schema', 'completed', 'inputs', 'bundle'}, 'reuse receipt')
        if receipt['schema'] != SCHEMA or receipt['completed'] != COMPLETED:
            raise ValueError('reuse receipt lacks complete entry success')
        inputs = materials.require_keys(receipt['inputs'],
            {'eligible', 'report_format', 'files', 'execution'}, 'reuse inputs')
        if (inputs['eligible'] is not True or not isinstance(inputs['files'], dict)
                or 'lean-toolchain' not in inputs['files']):
            raise ValueError('incomplete reuse inputs')
        for file in inputs['files'].values():
            materials.require_keys(file, {'sha256', 'mode'}, 'reuse input file')
            if (not publication.HEX.fullmatch(file['sha256']) or type(file['mode']) is not int
                    or not 0 <= file['mode'] <= 0o7777):
                raise ValueError('invalid reuse input file')
        execution = materials.require_keys(inputs['execution'],
            {'toolchain', 'tools', 'platform', 'environment'}, 'reuse execution')
        if (execution['toolchain'] != 'lean-toolchain' or not isinstance(execution['tools'], list)
                or sorted(execution['tools']) != sorted(publication.selection.REPORT_EXECUTION['tools'])):
            raise ValueError('incomplete reuse execution')
        for field in ('platform', 'environment'):
            values = materials.require_keys(execution[field],
                set(publication.selection.REPORT_EXECUTION[field]), 'reuse execution ' + field)
            if any(not isinstance(value, str) for value in values.values()):
                raise ValueError('invalid reuse execution ' + field)
        if receipt['bundle'] != bundle_hashes(report):
            raise ValueError('reuse receipt bundle mismatch')
        value = inputs['report_format']
        if not isinstance(value, str) or not value:
            raise ValueError('missing report format')
        return dict(report_format=value, compatible=value == publication.selection.REPORT_FORMAT)
    except INVALID_SEED:
        return dict(report_format='unavailable', compatible=False)


def recover_and_reuse(repository, report, output):
    """Restore and consume a checked seed under the existing private-cache lock."""
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts/worktree'))
    from lean_cache_release import cache_guard
    # Authored registration failures must precede optional network recovery.
    capture(repository)
    local = seed_format(report)
    try:
        with cache_guard(repository):
            checked = seed_format(report)
            if not checked['compatible']:
                recovery_environment = os.environ.copy()
                recovery_environment['STRATALINT_ACTIONS_CACHE_SEEDED'] = '0'
                fetched = subprocess.run(['/bin/bash', str(repository / 'tools/scripts/worktree/lean-cache-publish.sh'),
                    'fetch', '--mode', 'production', '--refresh-stale', '--writer-owned'],
                    cwd=repository, env=recovery_environment)
                report = repository / '.lake/build/stratalint/raw-lean-report.json'
                checked = seed_format(report)
                if not checked['compatible']:
                    raise CacheIncompatible(local['report_format'], checked['report_format'],
                                            'fetch-unavailable' if fetched.returncode else 'seed-incompatible')
            # Input differences select Lake's incremental path, not a new cache key.
            return reuse(repository, report, output)
    except BlockingIOError as error:
        raise CacheIncompatible(local['report_format'], 'unavailable', 'cache-busy') from error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('probe', 'reuse', 'capture', 'seal'))
    parser.add_argument('--repository', required=True, type=Path)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--snapshot', type=Path)
    parser.add_argument('--cache-miss-policy', choices=('reuse-or-build', 'fetch-or-fail'),
                        default='reuse-or-build')
    parser.add_argument('--diagnostics', action='store_true',
                        help='emit probe mismatch warnings to stderr while retaining JSON stdout')
    args = parser.parse_args()
    if args.command in ('probe', 'reuse', 'seal') and args.report is None:
        parser.error('--report is required')
    if args.command == 'reuse' and args.output is None:
        parser.error('--output is required')
    if args.command in ('capture', 'seal') and args.snapshot is None:
        parser.error('--snapshot is required')
    if args.command == 'capture':
        args.snapshot.write_bytes(materials.canonical_json(capture(args.repository)))
    elif args.command == 'seal':
        seal(args.repository, args.report, publication.read_json(args.snapshot.read_bytes()))
    elif args.command == 'probe':
        result = probe(args.repository, args.report)
        print(json.dumps(result, separators=(',', ':')))
        if args.diagnostics:
            warn_mismatch(result, sys.stderr)
    else:
        result = (recover_and_reuse(args.repository, args.report, args.output)
                  if args.cache_miss_policy == 'fetch-or-fail'
                  else reuse(args.repository, args.report, args.output))
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
    except CacheIncompatible as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(4)
    except INVALID_SEED as error:
        print(f'lean-inspector-reuse: {error}', file=sys.stderr)
        raise SystemExit(1)
