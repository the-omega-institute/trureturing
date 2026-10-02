#!/usr/bin/env python3
"""Validate optional evidence that the complete report entry has no new work.

The report semantic version, the report-module and configuration inputs, the explicitly
registered execution environment and the complete five-piece report are sealed
only after defaults/report/publication succeed. Producer program bytes are not
part of the seal; the semantic version is their compatibility contract. A receipt selects no rules and grants no check success. A miss returns
to the normal Lake entry; malformed authored registration remains an error.
"""
import argparse
import contextlib
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

SCHEMA = 'stratalint-lean-report-reuse-v2'
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
    # incompatible program change must bump the explicit semantic version.
    paths = sorted(set(inputs.expand('report_modules') + inputs.expand('config_inputs')))
    files = {}
    for path in paths:
        source = inputs.safe_file(path)
        files[path] = dict(sha256=publication.digest(source), mode=stat.S_IMODE(source.stat().st_mode))
    return dict(eligible=True, semantic_version=inputs.data['report_cache_release_semantic_version'], files=files,
        execution=dict(toolchain=execution['toolchain'], tools=execution['tools'],
                       platform={name: getattr(platform, name)() for name in execution['platform']},
                       environment=environment))


def bundle_hashes(report):
    publication._require_bundle_files(report)
    return {suffix: publication.digest(publication.member(report, suffix)) for suffix in publication.SUFFIXES}


def load_receipt(report):
    path = publication.member(report, SUFFIX)
    if path.is_symlink() or not path.is_file():
        raise ValueError('reuse receipt is absent or nonregular')
    receipt = publication.read_json(path.read_bytes())
    materials.require_keys(receipt, {'schema', 'completed', 'inputs', 'bundle'}, 'reuse receipt')
    if receipt['schema'] != SCHEMA or receipt['completed'] != COMPLETED:
        raise ValueError('reuse receipt lacks complete entry success')
    return receipt


def seed_version(repository, report):
    """Read seed availability/version only; Lake still owns same-version changes."""
    current = publication.selection.Selection(repository).data['report_cache_release_semantic_version']
    try:
        receipt = load_receipt(report)
        publication._require_bundle_files(report)
        local = receipt['inputs']['semantic_version']
        if type(local) is not int or local <= 0:
            raise ValueError('seed semantic version is absent or invalid')
    except INVALID_SEED:
        return dict(local_version='unavailable', current_version=current, reason='seed-unavailable')
    return dict(local_version=local, current_version=current,
                reason='version-matched' if local == current else 'version-mismatch')


def read_receipt(report, captured):
    receipt = load_receipt(report)
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


def seal(repository, report, captured, owner_snapshot=None):
    current = capture(repository)
    if current != captured:
        if owner_snapshot is not None:
            cleanup_receipt(repository, report, owner_snapshot, writer_owned=True)
        raise ValueError('registered inputs changed during report entry')
    if not captured['eligible']:
        if owner_snapshot is not None:
            cleanup_receipt(repository, report, owner_snapshot, writer_owned=True)
        return
    # The caller reaches this only after Lake's default+report facet and normal
    # private publication have succeeded. Bind the exact published five pieces.
    write_receipt(report, captured)
    if owner_snapshot is not None:
        claim_receipt(report, owner_snapshot)


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
    def __init__(self, local, current, dev, reason):
        super().__init__(f'LEAN_REPORT_CACHE_INCOMPATIBLE local_version={local} '
                         f'current_version={current} dev_seed_version={dev} reason={reason}\n'
                         'Rebuild explicitly with make lean-report REBUILD_REPORT_CACHE=1')


def cache_guard(repository):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts/worktree'))
    from lean_cache_release import cache_guard as guard
    return guard(repository)


def receipt_identity(report):
    try:
        info = publication.member(report, SUFFIX).lstat()
    except FileNotFoundError:
        return None
    return [info.st_dev, info.st_ino, info.st_mtime_ns, info.st_size]


def claim_receipt(report, snapshot):
    """Record a receipt's identity while the caller holds writer ownership."""
    snapshot.write_text(json.dumps(receipt_identity(report)))


def cleanup_receipt(repository, report, snapshot, writer_owned=False):
    """Invalidate only the claimed receipt, without racing a subsequent writer."""
    if not snapshot.is_file():
        return
    identity = json.loads(snapshot.read_text())
    if identity is None:
        return
    try:
        with contextlib.nullcontext() if writer_owned else cache_guard(repository):
            if receipt_identity(report) == identity:
                publication.member(report, SUFFIX).unlink(missing_ok=True)
    except BlockingIOError:
        # Another writer owns the current output; this caller cannot invalidate it.
        return


def recover_and_reuse(repository, report, output, owner_snapshot=None):
    """Check, restore and consume the actual seed under private-cache ownership."""
    current = publication.selection.Selection(repository).data['report_cache_release_semantic_version']
    try:
        with cache_guard(repository):
            status = seed_version(repository, report)
            local = status['local_version']
            if status['reason'] != 'version-matched':
                # The parent owns the same exclusive guard used by Release fetch
                # and LeanCacheGuard. Its child must not reacquire that lock.
                recovery_environment = os.environ.copy()
                # A local recovery is an explicit fetch request.  Do not let
                # an inherited Actions seed marker turn it into a skipped
                # fetch before the release reader examines the dev snapshot.
                recovery_environment['STRATALINT_ACTIONS_CACHE_SEEDED'] = '0'
                fetched = subprocess.run(['/bin/bash', str(repository / 'tools/scripts/worktree/lean-cache-publish.sh'),
                                          'fetch', '--mode', 'production', '--refresh-stale', '--writer-owned'],
                                         cwd=repository, env=recovery_environment)
                if fetched.returncode:
                    raise CacheIncompatible(local, current, 'unavailable', 'fetch-unavailable')
                report = repository / '.lake/build/stratalint/raw-lean-report.json'
                status = seed_version(repository, report)
                if status['reason'] != 'version-matched':
                    raise CacheIncompatible(local, current, status['local_version'], status['reason'])
            # Same-version misses retain the existing Lake incremental path.
            # Snapshot/publish the checked seed before releasing ownership.
            result = reuse(repository, report, output)
            if not result['needs_lake'] and owner_snapshot is not None:
                claim_receipt(output, owner_snapshot)
            return result
    except BlockingIOError as error:
        raise CacheIncompatible('unavailable', current, 'unavailable', 'cache-busy') from error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('probe', 'reuse', 'capture', 'seal',
                                           'claim-receipt', 'cleanup-receipt'))
    parser.add_argument('--repository', required=True, type=Path)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--snapshot', type=Path)
    parser.add_argument('--owner-snapshot', type=Path)
    parser.add_argument('--writer-owned', action='store_true',
                        help='cleanup runs inside the native writer guard')
    parser.add_argument('--diagnostics', action='store_true',
                        help='emit probe mismatch warnings to stderr while retaining JSON stdout')
    parser.add_argument('--cache-miss-policy', choices=('reuse-or-build', 'fetch-or-fail'),
                        default='reuse-or-build', help='policy for the reuse consumer')
    args = parser.parse_args()
    if args.command in ('probe', 'reuse', 'seal', 'claim-receipt', 'cleanup-receipt') and args.report is None:
        parser.error('--report is required')
    if args.command == 'reuse' and args.output is None:
        parser.error('--output is required')
    if args.command in ('capture', 'seal') and args.snapshot is None:
        parser.error('--snapshot is required')
    if args.command in ('claim-receipt', 'cleanup-receipt') and args.owner_snapshot is None:
        parser.error('--owner-snapshot is required')
    if args.command == 'claim-receipt':
        claim_receipt(args.report, args.owner_snapshot)
    elif args.command == 'cleanup-receipt':
        cleanup_receipt(args.repository, args.report, args.owner_snapshot, args.writer_owned)
    elif args.command == 'capture':
        args.snapshot.write_bytes(materials.canonical_json(capture(args.repository)))
    elif args.command == 'seal':
        with cache_guard(args.repository):
            seal(args.repository, args.report, publication.read_json(args.snapshot.read_bytes()),
                 args.owner_snapshot)
    elif args.command == 'probe':
        result = probe(args.repository, args.report)
        print(json.dumps(result, separators=(',', ':')))
        if args.diagnostics:
            warn_mismatch(result, sys.stderr)
    else:
        if args.cache_miss_policy == 'fetch-or-fail':
            result = recover_and_reuse(args.repository, args.report, args.output, args.owner_snapshot)
        else:
            with cache_guard(args.repository):
                result = reuse(args.repository, args.report, args.output)
                if not result['needs_lake'] and args.owner_snapshot is not None:
                    claim_receipt(args.output, args.owner_snapshot)
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
        print(error, file=sys.stderr)
        raise SystemExit(4)
    except INVALID_SEED as error:
        print(f'lean-inspector-reuse: {error}', file=sys.stderr)
        raise SystemExit(1)
