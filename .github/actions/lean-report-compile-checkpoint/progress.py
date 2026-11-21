"""Save finished Lake compiler outputs changed since the immutable project seed was restored."""
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/scripts/worktree'))
from lean_actions_shards import archive_sha, extract_payload, install_continuation, transport_payload, write_payload
from lean_cache_release import cache_guard
from lean_release_index import valid_artifact_description

BUILD = ROOT / '.lake/build'
PACKAGES = ('', 'reg', 'lean-inspector/interface', 'lean-inspector/producer', 'lean-inspector/reg')
FIELDS = {'o': ('olean', 'olean.server', 'olean.private'), 'i': ('ilean',),
          'c': ('c',), 'b': ('bc',), 'r': ('ir',), 'rs': ('ir.sig',)}


def trace_files():
    for package in PACKAGES:
        base = BUILD / package
        for tree in ('bin', 'lib/lean', 'ir'):
            directory = base / tree
            for path in directory.rglob('*.trace'):
                if path.is_file() and not path.is_symlink():
                    yield base, tree, path


def version(path):
    info = path.stat()
    return [info.st_ino, info.st_size, info.st_mtime_ns]


def output_group(base, tree, trace):
    metadata = json.loads(trace.read_bytes())
    outputs = metadata.get('outputs') if isinstance(metadata, dict) else None
    files = [trace]
    if tree == 'lib/lean' and isinstance(outputs, dict):
        if not valid_artifact_description(outputs) or outputs.keys() - (FIELDS.keys() | {'m'}):
            return []
        stem = trace.relative_to(base / tree).with_suffix('')
        for key, extensions in FIELDS.items():
            if key not in outputs:
                continue
            values = outputs[key] if key == 'o' else [outputs[key]]
            if not isinstance(values, list) or not values:
                return []
            for descriptor in values:
                if not isinstance(descriptor, str):
                    return []
                digest, _, extension = descriptor.partition('.')
                if extension not in extensions:
                    return []
                directory = 'ir' if key in ('c', 'b') else tree
                files.extend(verified_output(base / directory / (str(stem) + '.' + extension), digest))
    elif tree in ('bin', 'ir') and isinstance(outputs, str):
        files.extend(verified_output(trace.with_suffix(''), outputs.partition('.')[0]))
    else:
        return []
    # Lake writes the successful trace after its outputs. A subsequent interrupted
    # rebuild must not validate new bytes using the preceding successful trace.
    completed = trace.stat().st_mtime_ns
    return files if all(p.stat().st_mtime_ns <= completed for p in files) else []


def verified_output(path, digest):
    sidecar = Path(str(path) + '.hash')
    if (not re.fullmatch('[0-9a-f]{16}', digest) or not path.is_file() or path.is_symlink()
            or sidecar.is_symlink() or sidecar.read_text().strip() != digest):
        raise ValueError('incomplete Lake output')
    return [path, sidecar]


def identity():
    coordinates = ('GITHUB_REPOSITORY', 'GITHUB_REF', 'GITHUB_SHA', 'GITHUB_RUN_ID', 'RUNNER_OS', 'RUNNER_ARCH')
    return {key: os.environ[key] for key in coordinates}


def seeds():
    return {key: os.environ[key] for key in ('PROJECT_SEED', 'DEPENDENCY_SEED')}


def run(operation, directory):
    baseline = directory.parent / 'report-preparation-baseline.json'
    if operation == 'mark':
        with cache_guard(ROOT, shared=True):
            baseline.write_text(json.dumps({str(p.relative_to(BUILD)): version(p) for _, _, p in trace_files()}))
        return
    record = directory / 'manifest.json'
    if operation == 'save':
        before = json.loads(baseline.read_text())
        files = set()
        groups = 0
        with cache_guard(ROOT, shared=True):
            for base, tree, path in trace_files():
                if before.get(str(path.relative_to(BUILD))) == version(path):
                    continue
                try:
                    group = output_group(base, tree, path)
                except (ValueError, FileNotFoundError):
                    # An interrupted child can leave an unfinished trace or output.
                    continue
                if group:
                    groups += 1
                    files.update(str(p.relative_to(BUILD)) for p in group)
            if not files:
                print('LEAN_REPORT_PROGRESS groups=0 bytes=0', flush=True)
                return
            digest = write_payload(ROOT, BUILD, files)
            directory.mkdir(parents=True, exist_ok=True)
            archive = directory / 'outputs.tar.gz'
            shutil.move(ROOT / transport_payload(digest), archive)
            record.write_text(json.dumps({'identity': identity(), 'seeds': seeds(), 'sha256': digest, 'groups': groups,
                                          'files': len(files)}))
            print(f'LEAN_REPORT_PROGRESS groups={groups} files={len(files)} bytes={archive.stat().st_size}')
        return
    if operation != 'restore':
        raise ValueError('expected mark, save or restore')
    header = json.loads(record.read_text())
    if header['identity'] != identity():
        raise ValueError('report preparation checkpoint has a different source, run or platform')
    if header['seeds'] != seeds():
        print('LEAN_REPORT_PROGRESS restored=0 reason=native-seed-changed')
        return
    archive = directory / 'outputs.tar.gz'
    if archive_sha(archive, None) != header['sha256']:
        raise ValueError('report preparation checkpoint digest mismatch')
    allowed = [str(Path('.lake/build') / package / tree) for package in PACKAGES for tree in ('bin', 'ir', 'lib/lean')]
    with cache_guard(ROOT), tempfile.TemporaryDirectory(dir=ROOT / '.lake') as temp:
        stage = Path(temp)
        paths = set()
        extract_payload(archive, stage / 'new', allowed, paths)
        if not paths or len(paths) != header['files']:
            raise ValueError('incomplete report preparation checkpoint')
        install_continuation(BUILD, stage / 'new', paths, stage / 'old')
    print(f'LEAN_REPORT_PROGRESS restored={len(paths)} bytes={archive.stat().st_size}')


if __name__ == '__main__':
    run(sys.argv[1], Path(sys.argv[2]))
