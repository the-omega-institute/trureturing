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
from contextlib import nullcontext
import json
import os
from pathlib import Path
import platform
import re
import shlex
import subprocess
import sys
import tempfile
import zipfile
import zlib

import materials
import publication

SCHEMA = 'stratalint-lean-report-reuse-v4'
BASE_SCHEMA = 'stratalint-lean-report-seed-base-v2'
BASE_RECORD = '.lake/lean-report-seed-base.json'
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
        # Git records only the owner executable bit; other permission bits
        # differ between checkouts of one commit and do not change report bytes.
        mode = 0o755 if source.stat().st_mode & 0o100 else 0o644
        files[path] = dict(sha256=publication.digest(source), mode=mode)
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


def _git(repository, *arguments):
    return subprocess.run(['git', '-C', str(repository), *arguments], check=True,
                          capture_output=True, text=True).stdout.strip()


def canonical_seed(repository):
    return repository / '.lake/build/stratalint/raw-lean-report.json'


def seed_identity(report):
    """Bind provenance to the complete installed bundle and success receipt."""
    try:
        return publication.bundle_identity(report, (*publication.SUFFIXES, SUFFIX))
    except INVALID_SEED:
        return None


def read_seed_base(repository):
    """Read the optional production/restore provenance record."""
    path = repository / BASE_RECORD
    try:
        record = publication.read_json(path.read_bytes())
        if not isinstance(record, dict):
            return None
        commit = record.get('producer_commit_sha')
        if (record.get('schema') != BASE_SCHEMA or not isinstance(commit, str)
                or re.fullmatch(r'[0-9a-f]{40}', commit) is None
                or record.get('seed_sha256') is None
                or record['seed_sha256'] != seed_identity(canonical_seed(repository))):
            return None
        return commit
    except (OSError, UnicodeError, ValueError, TypeError, KeyError):
        return None


def invalidate_seed_base(repository):
    """A different seed cannot inherit the previous seed's provenance."""
    (repository / BASE_RECORD).unlink(missing_ok=True)


def maintain_unknown_seed_base(repository):
    """Removing an already-untrusted record cannot change report acceptance."""
    try:
        invalidate_seed_base(repository)
    except OSError as error:
        return dict(reason='unknown-base-removal-failed', detail=str(error))
    return None


def record_seed_base(repository, commit=None):
    """Record a validated seed base only for a clean dev main checkout."""
    try:
        branch = _git(repository, 'symbolic-ref', '--quiet', '--short', 'HEAD')
        head = _git(repository, 'rev-parse', '--verify', 'HEAD')
        status = _git(repository, 'status', '--porcelain', '--untracked-files=normal')
        git_dir = Path(_git(repository, 'rev-parse', '--git-dir'))
        common_dir = Path(_git(repository, 'rev-parse', '--git-common-dir'))
        git_dir = (repository / git_dir if not git_dir.is_absolute() else git_dir).resolve()
        common_dir = (repository / common_dir if not common_dir.is_absolute() else common_dir).resolve()
        source = head if commit is None else commit
        identity = seed_identity(canonical_seed(repository))
        if (branch != 'dev' or status or git_dir != common_dir
                or re.fullmatch(r'[0-9a-f]{40}', source) is None or identity is None):
            invalidate_seed_base(repository)
            return False
        path = repository / BASE_RECORD
        path.parent.mkdir(parents=True, exist_ok=True)
        fd, temporary = tempfile.mkstemp(prefix='.seed-base.', dir=path.parent)
        try:
            with os.fdopen(fd, 'wb') as target:
                target.write(materials.canonical_json({
                    'schema': BASE_SCHEMA, 'producer_commit_sha': source,
                    'seed_sha256': identity}))
            os.replace(temporary, path)
        finally:
            Path(temporary).unlink(missing_ok=True)
        return True
    except (OSError, subprocess.SubprocessError, ValueError, UnicodeError):
        invalidate_seed_base(repository)
        return False


def publication_guard(repository, report):
    """Canonical writers share the restore guard; custom outputs own no cache seed."""
    if report.resolve() != canonical_seed(repository).resolve():
        return nullcontext()
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts/worktree'))
    from lean_cache_release import cache_guard
    return cache_guard(repository)


def observe_receipt(repository, report, receipt_snapshot):
    """Capture the entry's existing receipt without changing the generation."""
    with publication_guard(repository, report):
        receipt = publication.member(report, SUFFIX)
        if not receipt.is_symlink() and receipt.is_file():
            receipt_snapshot.write_text(publication.digest(receipt) + '\n')


def prepare(repository, report, receipt_snapshot=None):
    """Invalidate production metadata only after claiming the output's guard."""
    with publication_guard(repository, report):
        maintenance = None
        if report.resolve() == canonical_seed(repository).resolve():
            if read_seed_base(repository) is None:
                maintenance = maintain_unknown_seed_base(repository)
            else:
                invalidate_seed_base(repository)
        publication.member(report, SUFFIX).unlink(missing_ok=True)
        if receipt_snapshot is not None:
            receipt_snapshot.unlink(missing_ok=True)
        return maintenance


def invalidate_receipt(repository, report, receipt_snapshot):
    """A failed invocation may invalidate only the receipt it observed."""
    if not receipt_snapshot.is_file():
        return
    observed = receipt_snapshot.read_text().strip()
    if re.fullmatch(r'[0-9a-f]{64}', observed) is None:
        raise ValueError('invalid cleanup receipt identity')
    with publication_guard(repository, report):
        receipt = publication.member(report, SUFFIX)
        if not receipt.is_symlink() and receipt.is_file() and publication.digest(receipt) == observed:
            receipt.unlink()


def seal(repository, report, captured, produced_sha256):
    with publication_guard(repository, report):
        _seal(repository, report, captured, produced_sha256)


def _seal(repository, report, captured, produced_sha256):
    """Seal within the canonical writer's existing exclusive section."""
    if produced_sha256 is None or publication.bundle_identity(report) != produced_sha256:
        raise ValueError('published report generation changed before seal')
    canonical = report.resolve() == canonical_seed(repository).resolve()
    if canonical:
        invalidate_seed_base(repository)
    current = capture(repository)
    if current != captured:
        publication.member(report, SUFFIX).unlink(missing_ok=True)
        raise ValueError('registered inputs changed during report entry')
    if not captured['eligible']:
        publication.member(report, SUFFIX).unlink(missing_ok=True)
        return
    write_receipt(report, captured)
    if canonical and not record_seed_base(repository):
        invalidate_seed_base(repository)


def reuse(repository, report, output, receipt_snapshot=None):
    with publication_guard(repository, output):
        return _reuse(repository, report, output, receipt_snapshot)


def _reuse(repository, report, output, receipt_snapshot=None):
    captured = capture(repository)
    if not captured['eligible']:
        return miss(captured['reason'])
    canonical = output.resolve() == canonical_seed(repository).resolve()
    canonical_source = report.resolve() == canonical_seed(repository).resolve()
    base = read_seed_base(repository) if canonical and canonical_source else None
    maintenance = (maintain_unknown_seed_base(repository)
                   if canonical and canonical_source and base is None else None)
    try:
        # The receipt binds bundle bytes that were validated when produced; like
        # a restored olean they are reused as is. Publication still stages a
        # private snapshot that must match the receipt and current inputs.
        receipt = read_receipt(report, captured)
        coordinates = publication.coordinates(repository)
        if canonical and not canonical_source:
            invalidate_seed_base(repository)
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
        if canonical and base is not None and not record_seed_base(repository, base):
            invalidate_seed_base(repository)
    except INVALID_SEED as error:
        publication.member(output, SUFFIX).unlink(missing_ok=True)
        if receipt_snapshot is not None:
            receipt_snapshot.unlink(missing_ok=True)
        return miss('seed-rejected', error)
    if receipt_snapshot is not None:
        receipt_snapshot.write_text(publication.digest(publication.member(output, SUFFIX)) + '\n')
    result = dict(needs_lake=False, reason='complete-entry-reused')
    if maintenance is not None:
        result['base_maintenance'] = maintenance
    return result


class CacheIncompatible(ValueError):
    def __init__(self, local, restored, reason, remediation=None):
        if remediation is None:
            remediation = 'Restore with make lean-cache-from-github-without-mathlib REFRESH_STALE=1'
        super().__init__(f'LEAN_REPORT_CACHE_INCOMPATIBLE local_format={local} '
                         f'current_format={publication.selection.REPORT_FORMAT} '
                         f'restored_format={restored} reason={reason}\n'
                         f'{remediation} '
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


def _ancestry(repository, ancestor, descendant):
    result = subprocess.run(['git', '-C', str(repository), 'merge-base', '--is-ancestor',
                             ancestor, descendant], check=False, capture_output=True)
    if result.returncode == 0:
        return True
    if result.returncode != 1 or _git(repository, 'rev-parse', '--is-shallow-repository') == 'true':
        return None
    return False


def _seed_mismatch(report, captured):
    try:
        read_receipt(report, captured)
    except InputMismatch as error:
        return error
    return None


def _seed_decision(action, reason, **fields):
    payload = {'action': action, 'reason': reason, **fields}
    print('LEAN_REPORT_SEED_DECISION ' + json.dumps(payload, sort_keys=True,
                                                   separators=(',', ':')), flush=True)


def _refresh_stale_seed(repository, report):
    """Optionally replace a stale compatible seed with a strictly newer Release base."""
    if report.resolve() != canonical_seed(repository).resolve():
        _seed_decision('keep', 'non-canonical-seed')
        return report
    captured = capture(repository)
    if not captured['eligible']:
        _seed_decision('keep', captured['reason'])
        return report
    mismatch = _seed_mismatch(report, captured)
    if mismatch is None:
        _seed_decision('keep', 'seed-current')
        return report
    if os.environ.get('GITHUB_ACTIONS') == 'true':
        _seed_decision('keep', 'ci-release-seeds-disabled')
        return report
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts/worktree'))
    from lean_cache_release import checkout_topology, latest_snapshot, operation_deadline, partition_path
    try:
        linked, _ = checkout_topology(repository)
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        _seed_decision('keep', 'dev-main-unavailable', detail=str(error))
        return report
    if linked:
        _seed_decision('keep', 'not-dev-main-checkout')
        return report
    try:
        branch = _git(repository, 'symbolic-ref', '--quiet', '--short', 'HEAD')
    except subprocess.CalledProcessError as error:
        _seed_decision('keep', 'detached-checkout' if error.returncode == 1
                       else 'dev-main-unavailable')
        return report
    if branch != 'dev':
        _seed_decision('keep', 'not-dev-main-checkout')
        return report
    try:
        status = _git(repository, 'status', '--porcelain', '--untracked-files=normal')
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        _seed_decision('keep', 'dev-main-unavailable', detail=str(error))
        return report
    if status:
        _seed_decision('keep', 'unclean-checkout')
        return report
    base = read_seed_base(repository)
    if base is None:
        _seed_decision('keep', 'local-base-unknown')
        return report
    try:
        candidate = latest_snapshot(repository, partition_path(repository), operation_deadline())
    except (OSError, EOFError, ImportError, ValueError, KeyError, TypeError, AttributeError, IndexError,
            subprocess.SubprocessError) as error:
        _seed_decision('keep', 'release-manifest-unavailable', detail=str(error))
        return report
    if candidate is None:
        _seed_decision('keep', 'no-published-snapshot')
        return report
    tag, release = candidate
    try:
        head = _git(repository, 'rev-parse', '--verify', 'HEAD')
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        _seed_decision('keep', 'head-unavailable', detail=str(error), release=release)
        return report
    reachable = _ancestry(repository, release, head)
    if reachable is not True:
        _seed_decision('keep', 'release-head-ancestry-unprovable' if reachable is None
                       else 'release-not-head-ancestor', release=release, head=head)
        return report
    newer = _ancestry(repository, base, release)
    if base == release or newer is not True:
        _seed_decision('keep', 'local-base-ancestry-unprovable' if newer is None
                       else 'release-not-newer', local=base, release=release)
        return report
    environment = os.environ.copy()
    environment['STRATALINT_ACTIONS_CACHE_SEEDED'] = '0'
    try:
        fetched = subprocess.run(['/bin/bash', str(repository / 'tools/scripts/worktree/lean-cache-publish.sh'),
            'fetch', '--mode', 'production', '--refresh-stale', '--writer-owned',
            '--approved-tag', tag, '--approved-producer', release],
            cwd=repository, env=environment, capture_output=True, text=True)
    except (OSError, subprocess.SubprocessError) as error:
        _seed_decision('keep', 'release-download-failed', release=release, detail=str(error))
        return report
    print(fetched.stdout, end='', flush=True)
    print(fetched.stderr, end='', file=sys.stderr, flush=True)
    outcomes = [publication.read_json(line.partition(' ')[2].encode())
                for line in fetched.stdout.splitlines() if line.startswith('LEAN_CACHE_FETCH ')]
    failed_rollback = next((outcome for outcome in outcomes if isinstance(outcome, dict)
                            and outcome.get('status') == 'rollback-failed'), None)
    if failed_rollback is not None:
        _seed_decision('fail', 'release-rollback-failed', release=release,
                       backup=failed_rollback['backup'], detail=failed_rollback['reason'])
        raise CacheIncompatible(publication.selection.REPORT_FORMAT,
                                seed_format(report)['report_format'],
                                'release-rollback-failed',
                                'Retained recovery backup: ' + failed_rollback['backup'])
    installed = any(isinstance(outcome, dict) and outcome.get('status') == 'unpacked'
        and outcome.get('resolved') == tag and outcome.get('producer_commit_sha') == release
        and outcome.get('installed') == ['build'] for outcome in outcomes)
    if not installed and fetched.returncode:
        _seed_decision('keep', 'release-download-failed', release=release,
                       exit=fetched.returncode)
        return report
    if not installed:
        _seed_decision('keep', 'release-installation-skipped', release=release, tag=tag)
        return report
    _seed_decision('fetch', 'newer-release', local=base, release=release, tag=tag)
    return repository / '.lake/build/stratalint/raw-lean-report.json'


def refresh_stale_seed(repository):
    """Warm-donor hook: transport misses keep the seed; failed rollback blocks."""
    report = repository / '.lake/build/stratalint/raw-lean-report.json'
    try:
        if seed_format(report)['compatible']:
            sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts/worktree'))
            from lean_cache_release import cache_guard
            with cache_guard(repository):
                _refresh_stale_seed(repository, report)
                checked = seed_format(report)
                if not checked['compatible']:
                    raise CacheIncompatible(publication.selection.REPORT_FORMAT,
                                            checked['report_format'], 'seed-unavailable-after-refresh')
        else:
            _seed_decision('keep', 'seed-unavailable')
    except CacheIncompatible:
        raise
    except (OSError, EOFError, ImportError, ValueError, KeyError, TypeError, AttributeError, IndexError,
            subprocess.SubprocessError) as error:
        _seed_decision('keep', 'stale-seed-refresh-unavailable', detail=str(error))
    return 0


def recover_and_reuse(repository, report, output, receipt_snapshot=None):
    """Restore and consume a checked seed under the existing private-cache lock."""
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts/worktree'))
    from lean_cache_release import cache_guard, checkout_topology, warm_dev_remediation
    # Authored registration failures must precede optional network recovery.
    capture(repository)
    local = seed_format(report)
    try:
        linked, main_checkout = checkout_topology(repository)
    except ValueError as error:
        raise CacheIncompatible(local['report_format'], 'unavailable', 'checkout-undetermined',
                                str(error)) from error
    remediation = None
    if linked:
        warm_report = ("sync dev and warm the dev cache in this repository's dev main checkout: "
                       'make warm-donor && make lean-report there '
                       '(its location cannot be determined from this worktree); then reseed: rm -rf -- '
                       if main_checkout is None else warm_dev_remediation(main_checkout)
                       + ' && make -C ' + shlex.quote(str(main_checkout)) + ' lean-report'
                       + '; then reseed from the warm main checkout: rm -rf -- ')
        remediation = (warm_report
                       + shlex.quote(str(repository / '.lake')) + ' && make -C '
                       + shlex.quote(str(repository)) + ' lean-cache-ensure')
    try:
        with cache_guard(repository):
            checked = seed_format(report)
            if not checked['compatible']:
                if linked:
                    report = repository / '.lake/build/stratalint/raw-lean-report.json'
                    checked = seed_format(report)
                    if not checked['compatible']:
                        raise CacheIncompatible(local['report_format'], checked['report_format'],
                                                'linked-worktree', remediation)
                else:
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
            elif not linked:
                report = _refresh_stale_seed(repository, report)
                checked = seed_format(report)
                if not checked['compatible']:
                    raise CacheIncompatible(local['report_format'], checked['report_format'],
                                            'seed-unavailable-after-refresh')
            # Input differences select Lake's incremental path, not a new cache key.
            return _reuse(repository, report, output, receipt_snapshot)
    except BlockingIOError as error:
        raise CacheIncompatible(local['report_format'], 'unavailable', 'cache-busy', remediation) from error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('probe', 'reuse', 'capture', 'prepare', 'observe-receipt',
                                           'invalidate-receipt', 'seal', 'refresh-stale-seed'))
    parser.add_argument('--repository', required=True, type=Path)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--snapshot', type=Path)
    parser.add_argument('--receipt-snapshot', type=Path,
                        help='invocation-local receipt identity for generation-scoped failure cleanup')
    parser.add_argument('--bundle-sha256', help='complete bundle identity returned by publication')
    parser.add_argument('--cache-miss-policy', choices=('reuse-or-build', 'fetch-or-fail'),
                        default='reuse-or-build')
    parser.add_argument('--diagnostics', action='store_true',
                        help='emit probe mismatch warnings to stderr while retaining JSON stdout')
    args = parser.parse_args()
    if args.command != 'refresh-stale-seed' and args.report is None:
        parser.error('--report is required')
    if args.command == 'reuse' and args.output is None:
        parser.error('--output is required')
    if args.command in ('capture', 'seal') and args.snapshot is None:
        parser.error('--snapshot is required')
    if args.command in ('observe-receipt', 'invalidate-receipt') and args.receipt_snapshot is None:
        parser.error('--receipt-snapshot is required')
    if args.command == 'seal' and (args.bundle_sha256 is None
            or re.fullmatch(r'[0-9a-f]{64}', args.bundle_sha256) is None):
        parser.error('--bundle-sha256 must be the produced bundle identity')
    if args.command == 'refresh-stale-seed':
        return refresh_stale_seed(args.repository)
    if args.command == 'capture':
        captured = capture(args.repository)
        args.snapshot.write_bytes(materials.canonical_json(captured))
    elif args.command == 'prepare':
        maintenance = prepare(args.repository, args.report, args.receipt_snapshot)
        if maintenance is not None:
            print('LEAN_REPORT_BASE_MAINTENANCE ' + json.dumps(maintenance, separators=(',', ':')))
    elif args.command == 'observe-receipt':
        try:
            observe_receipt(args.repository, args.report, args.receipt_snapshot)
        except BlockingIOError as error:
            if args.cache_miss_policy == 'fetch-or-fail':
                raise CacheIncompatible(seed_format(args.report)['report_format'],
                                        'unavailable', 'cache-busy') from error
            raise
    elif args.command == 'invalidate-receipt':
        invalidate_receipt(args.repository, args.report, args.receipt_snapshot)
    elif args.command == 'seal':
        seal(args.repository, args.report, publication.read_json(args.snapshot.read_bytes()),
             args.bundle_sha256)
    elif args.command == 'probe':
        result = probe(args.repository, args.report)
        print(json.dumps(result, separators=(',', ':')))
        if args.diagnostics:
            warn_mismatch(result, sys.stderr)
    else:
        result = (recover_and_reuse(args.repository, args.report, args.output, args.receipt_snapshot)
                  if args.cache_miss_policy == 'fetch-or-fail'
                  else reuse(args.repository, args.report, args.output, args.receipt_snapshot))
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
