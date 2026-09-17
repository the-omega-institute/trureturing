#!/usr/bin/env python3
"""Guarded ST0-ST26 insertion. Requires the complete original local worktree.
Dry-run by default; --write edits only on a non-protected branch. No commit,
push, network call, Lean build, or CI operation is performed.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import tempfile

TARGET = Path('docs/develop/theory/QUANTUM-REALITY.md')
BASE_BLOB = '09df8199fd2cd36a90a8df1cd3dfd6cbe3962b32'
ANCHOR = '# 钟记录、径向俘获与视界红移\n'.encode()
CHUNKS = (
    ('QUANTUM-REALITY.ST0-ST9.insert.md', '32a80c1f8a607606e04b9f9edf4ba9be6ae6a04bed4298e070221f07969cad88', b'<a id="string-observer-integration"></a>'),
    ('QUANTUM-REALITY.ST10-ST18.insert.md', '9d2433bfac84a3a1e34963800c6ad6c35fab5694333e3d86956067d9c5d1259d', b'<a id="string-observer-born-geometry"></a>'),
    ('QUANTUM-REALITY.ST19-ST26.insert.md', 'e9c0883135637b0401d290361bb1d771117b11aa4180d8477f93964bae9373a6', b'<a id="string-observer-leakage-global-geometry"></a>'),
)


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def load_chunks(directory: Path) -> list[bytes]:
    chunks = []
    for name, sha, marker in CHUNKS:
        data = (directory/name).read_bytes()
        data.decode('utf-8')
        # The remotely retained ST0-ST9 copy omits only its last blank line.
        if name == CHUNKS[0][0] and blob_sha(data) == '910ca3fcf62ec35c2cd01eb4f623ff7ba57c40af':
            data += b'\n'
        if hashlib.sha256(data).hexdigest() != sha or data.count(marker) != 1:
            raise ValueError(f'Insertion file changed: {name}')
        chunks.append(data)
    return chunks


def plan(current: bytes, chunks: list[bytes], expected_base: str = BASE_BLOB) -> tuple[bytes, int]:
    """Pure transformation. expected_base is only parameterized for fixture tests."""
    if len(chunks) != len(CHUNKS) or current.count(ANCHOR) != 1:
        raise ValueError('Expected all chunks and one original chapter-31 anchor.')
    counts = [current.count(row[2]) for row in CHUNKS]
    if any(n > 1 for n in counts):
        raise ValueError('Duplicate insertion marker.')
    count = sum(counts)
    if counts != [1]*count+[0]*(len(CHUNKS)-count):
        raise ValueError('Existing insertions are not a complete ordered prefix.')
    existing = b''.join(chunks[:count])
    if existing:
        if current.count(existing) != 1:
            raise ValueError('Partial, edited, separated or reordered insertion.')
        at = current.index(existing)
        if not current[at+len(existing):].startswith(ANCHOR):
            raise ValueError('Existing insertion is not at the original anchor.')
        base = current[:at]+current[at+len(existing):]
    else:
        base = current
    if blob_sha(base) != expected_base:
        raise ValueError('Reviewed original blob differs; reconcile source drift first.')
    combined = b''.join(chunks)
    result = base.replace(ANCHOR, combined+ANCHOR, 1)
    if result.replace(combined, b'', 1) != base:
        raise AssertionError('Original-byte preservation failed.')
    return result, count


def git(repo: Path, *args: str) -> str:
    return subprocess.run(['git', '-C', str(repo), *args], check=True,
                          capture_output=True, text=True).stdout.strip()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    repo = args.repo.resolve(strict=True)
    target = repo/TARGET
    if target.is_symlink() or not target.is_file() or not target.resolve().is_relative_to(repo):
        raise ValueError('Target must be a regular non-symlink file within the worktree.')
    chunks = load_chunks(Path(__file__).resolve().parent)
    current = target.read_bytes()
    result, count = plan(current, chunks)
    branch = git(repo, 'branch', '--show-current')
    report = dict(previous_chunks=count, result_chunks=3, branch=branch,
                  target=TARGET.as_posix(), source_blob=blob_sha(current),
                  result_blob=blob_sha(result), bytes_before=len(current),
                  bytes_after=len(result), original_bytes_preserved=True, written=False)
    if args.write and result != current:
        if not branch or branch in {'dev', 'main', 'master'}:
            raise ValueError('Write only on a dedicated research branch.')
        git(repo, 'ls-files', '--error-unmatch', '--', TARGET.as_posix())
        if git(repo, 'status', '--porcelain', '--', TARGET.as_posix()):
            raise ValueError('Target has staged or unstaged changes.')
        mode = stat.S_IMODE(target.stat().st_mode)
        fd, tmp = tempfile.mkstemp(prefix='.theory-ST-', dir=target.parent)
        try:
            with os.fdopen(fd, 'wb') as stream:
                stream.write(result)
                stream.flush()
                os.fsync(stream.fileno())
            os.chmod(tmp, mode)
            if target.is_symlink() or target.read_bytes() != current:
                raise ValueError('Target changed during preparation; write cancelled.')
            os.replace(tmp, target)
        finally:
            if os.path.exists(tmp):
                os.unlink(tmp)
        if target.read_bytes() != result:
            raise ValueError('Readback differs after write; inspect worktree.')
        report['written'] = True
    print(json.dumps(report, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        raise SystemExit(f'Application refused: {exc}') from exc
