#!/usr/bin/env python3
"""Reproducible, project-local instrumentation of the exact pinned Lean compiler.

All generated files live under build/compiler-origin. No downloaded executable,
source-name inference, host installation, or mutable global configuration.
"""
from __future__ import annotations
import fcntl
import ctypes
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import stat
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REVISION = 'd8b18978322de05a8f3dba51ef03cf5461676c17'
TOOLCHAIN = 'leanprover/lean4:v4.33.0'
SOURCES = {
    'Lean/Meta/Injective.lean': '713a9be2e7a0f9cc2ab76fa645be0ef2824287916e69a86178116fc880c7e5b5',
    'Lean/Meta/SizeOf.lean': '2d9ea458f26d4dbbaaadde4da136f578e7d4859c9a5058aee0d049669dd3c66d',
    'Lean/Meta/Eqns.lean': 'c031884b35f9fab9714ca5bcf1d92bc7d716350a8aaabdf38fb079f5055ea4a0',
    'Lean/Elab/PreDefinition/Structural/Eqns.lean': '3a59616fa759794298406303be1001f1b40f4e4357639f995b296485b2912c64',
    'Lean/Elab/PreDefinition/WF/Unfold.lean': 'a325299893dad6b83de7a4ebb6faf4ae836984edc6ac5cf0d3d9d213d5e471f7',
    'Lean/Elab/PreDefinition/WF/Eqns.lean': '99d3f26b55a0b719ad31a8e49629159a3b3b24cbf59eb7e9a637b00c20ec66e5',
    'Lean/Elab/PreDefinition/PartialFixpoint/Eqns.lean': '26ec3a1d6c9932c7ccd7fa4e7b6c81e17199101b5944422fe279aa5255e0b5c8',
    'Lean/Meta/CongrTheorems.lean': '2a24eae0954ff67bab815eab23dd595be020c0320086f070bae846947413d2db',
}


def sha(path):
    """Hash exact bytes incrementally without requiring hashlib.file_digest."""
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode() + b'\n'


def _clonefile(source, destination):
    """Clone one APFS file or directory, returning whether the syscall worked."""
    if sys.platform != 'darwin':
        return False
    try:
        clonefile = ctypes.CDLL(None, use_errno=True).clonefile
        clonefile.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_uint32]
        clonefile.restype = ctypes.c_int
        return clonefile(os.fsencode(source), os.fsencode(destination), 0) == 0
    except (AttributeError, OSError):
        return False


def clone_tree(source, destination):
    """Make a private tree from a validated producer tree.

    APFS clonefile keeps the fixture writable and private without copying the
    compiler's large immutable stock images. Other filesystems use the normal
    copy path; neither path creates links into the donor stage.
    """
    source, destination = Path(source), Path(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists() or destination.is_symlink():
        raise ValueError('compiler stage destination already exists')
    if not _clonefile(source, destination):
        shutil.copytree(source, destination, copy_function=shutil.copy2)


def validate_artifact_tree(directory, descriptor, *, read_only=False):
    """Validate the normal compiler receipt and exact current descriptor."""
    if directory.is_symlink():
        raise ValueError('compiler distribution is a symbolic link')
    receipt = directory / 'artifacts.json'
    expected = json.loads(receipt.read_text())
    required = {'bin/frontend', 'bin/lean', 'bin/leanc', 'driver.json', 'descriptor.json',
        'lib/lean/libLean.a', 'lib/lean/libLeanOrigin.a', 'lib/lean/Lean/CompanionOrigin.olean',
        'lib/lean/Lean/CompanionOrigin.o', 'LICENSE', 'LICENSES'}
    paths = list(directory.rglob('*'))
    if any(p.is_symlink() for p in paths):
        raise ValueError('compiler distribution contains a symbolic link')
    actual = {p.relative_to(directory).as_posix() for p in paths if p.is_file() and p != receipt}
    if not isinstance(expected, dict) or not required <= set(expected) or actual != set(expected):
        raise ValueError('compiler artifact receipt has an incomplete file set')
    if (directory / 'descriptor.json').read_bytes() != canonical(descriptor):
        raise ValueError('compiler descriptor mismatch')
    for relative, record in expected.items():
        path = directory / relative
        actual = dict(sha256=sha(path), mode=stat.S_IMODE(path.stat().st_mode))
        checked = dict(record, mode=record['mode'] & ~0o222) if read_only else record
        if actual != checked:
            raise ValueError('compiler artifact receipt mismatch: ' + relative)
    return expected


def stage(root, output):
    """Stage only the compiler owner's verified distribution, without links."""
    directory, identity = ensure(root)
    descriptor = inputs(root)[1]
    expected = validate_artifact_tree(directory, descriptor)
    destination = Path(output).resolve() / 'compiler-origin' / identity
    clone_tree(directory, destination)
    validate_artifact_tree(destination, descriptor)
    for relative in [*expected, 'artifacts.json']:
        path = destination / relative
        path.chmod(stat.S_IMODE(path.stat().st_mode) & ~0o222)
    return destination, identity


def restore(root, source):
    """Recheck the current recipe/stock inputs and restore private compiler bytes.

    A mismatched seed is rejected. The caller can then use ordinary ensure;
    no old descriptor or content-provided metadata grants compiler authority.
    """
    _, descriptor, identity = inputs(root)
    staged = Path(source).resolve() / 'compiler-origin' / identity
    expected = validate_artifact_tree(staged, descriptor, read_only=True)
    parent = root / 'build/compiler-origin'
    parent.mkdir(parents=True, exist_ok=True)
    with (parent / 'build.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        destination = parent / identity
        if destination.exists():
            validate_artifact_tree(destination, descriptor)
            return destination, identity
        try:
            clone_tree(staged, destination)
            for relative, record in expected.items():
                (destination / relative).chmod(record['mode'])
            (destination / 'artifacts.json').chmod(0o600)
            validate_artifact_tree(destination, descriptor)
            if inputs(root)[2] != identity:
                raise ValueError('compiler inputs changed during restore')
        except BaseException:
            if destination.exists():
                shutil.rmtree(destination)
            raise
    return destination, identity


def base_root(root):
    if (root / 'lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise ValueError('compiler origin requires the registered pinned toolchain')
    # Ignore inherited local overrides; ask elan for the explicitly named pin.
    executable = subprocess.check_output(['elan', 'which', 'lean'],
        cwd=root, env=dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN), text=True).strip()
    base = Path(executable).resolve().parents[1]
    if subprocess.check_output([str(base / 'bin/lean'), '--githash'], text=True).strip() != REVISION:
        raise ValueError('compiler revision mismatch')
    for name, expected in SOURCES.items():
        if sha(base / 'src/lean' / name) != expected:
            raise ValueError('pinned compiler source mismatch: ' + name)
    return base


@lru_cache(maxsize=None)
def base_inventory(base):
    # One invocation observes the immutable installed pin once. Repository and
    # recipe files are never memoized: edits are observed on every validation.
    return {p.relative_to(base).as_posix(): dict(sha256=sha(p), mode=stat.S_IMODE(p.stat().st_mode))
            for part in ('bin', 'lib', 'include', 'LICENSE', 'LICENSES')
            for p in ([base / part] if (base / part).is_file() else sorted((base / part).rglob('*')))
            if p.is_file()}


def inputs(root):
    base = base_root(root)
    recipe_dir = root / 'tools/lean-inspector/compiler'
    if not recipe_dir.is_dir():
        recipe_dir = HERE  # Explicit standalone fixture calls use this recipe.
    recipe = {p.name: sha(p) for p in sorted(recipe_dir.iterdir()) if p.is_file()}
    descriptor = dict(revision=REVISION, toolchain=TOOLCHAIN, base_inputs=base_inventory(base),
        source_inputs=SOURCES, recipe=recipe, system=platform.system(), machine=platform.machine(),
        build_tools={name: sha(shutil.which(name)) for name in ('patch', 'nm')},
        python=sha(sys.executable), deployment_target=os.environ.get('MACOSX_DEPLOYMENT_TARGET', '99.0'))
    return base, descriptor, hashlib.sha256(canonical(descriptor)).hexdigest()


def copy_material(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    # dyld resolves loader-relative paths through executable/image identity.
    # A shared inode can resolve through another compiler stage while that
    # stage is being removed. Keep Mach-O images private to their distribution.
    if sys.platform == 'darwin' and (src.parent.name == 'bin' or src.suffix == '.dylib'):
        # APFS clones retain separate inode/loader identity while sharing only
        # copy-on-write storage. Unsupported filesystems use a private copy.
        if not _clonefile(src.resolve(), dst):
            shutil.copy2(src, dst)
        return
    # Hard links are never changed in place. Every patched/replaced artifact is
    # unlinked first; immutable stock artifacts remain read-only inputs.
    try:
        os.link(src.resolve(), dst)
    except OSError:
        shutil.copy2(src, dst)


def patch_native_archive(base, directory, objects):
    """Replace exact module objects, including duplicate archive member names.

    Lake links with clang directly. Supplying only a leanc wrapper would leave
    native report/plugin consumers without the registry or generator overrides.
    Defined initializer symbols identify objects; no declaration classification
    is performed here.
    """
    ar = str(directory / 'bin/llvm-ar')
    archive = directory / 'lib/lean/libLeanOrigin.a'
    stock = base / 'lib/lean/libLean.a'
    members = subprocess.check_output([ar, 't', str(stock)], text=True).splitlines()
    candidates = {Path(name).stem + '.c.o.export' for name in SOURCES}
    occurrences = {}
    selected = []
    found = set()
    temp = directory / 'archive-members'
    temp.mkdir()
    for member in members:
        occurrences[member] = occurrences.get(member, 0) + 1
        if member not in candidates:
            continue
        subprocess.run([ar, 'xN', str(occurrences[member]), '--output', str(temp), str(stock), member], check=True)
        flags = ['-gU'] if sys.platform == 'darwin' else ['-g', '--defined-only']
        symbols = subprocess.check_output(['nm', *flags, str(temp / member)], text=True)
        names = {line.split()[-1].removeprefix('_') for line in symbols.splitlines() if line.split()}
        matches = [name for name in SOURCES if 'initialize_' + name[:-5].replace('/', '_') in names]
        if len(matches) > 1:
            raise ValueError('ambiguous compiler native object')
        if matches:
            name = matches[0]
            if name in found:
                raise ValueError('duplicate compiler native object')
            found.add(name)
            selected.append((member, occurrences[member]))
    if found != set(SOURCES):
        raise ValueError('incomplete pinned compiler native archive')
    shutil.copy2(stock, archive)
    for member, occurrence in sorted(selected, reverse=True):
        subprocess.run([ar, 'dN', str(occurrence), str(archive), member], check=True)
    additions = []
    for obj in objects:
        path = Path(obj)
        target = temp / ('origin_' + path.relative_to(directory / 'lib/lean').as_posix().replace('/', '_'))
        shutil.copy2(path, target)
        additions.append(str(target))
    subprocess.run([ar, 'qsD', str(archive), *additions], check=True)
    shutil.rmtree(temp)


def build(root, base, descriptor, identity):
    directory = root / 'build/compiler-origin' / identity
    receipt = directory / 'artifacts.json'
    try:
        validate_artifact_tree(directory, descriptor)
        return directory
    except (OSError, ValueError, KeyError, TypeError):
        # Optional damaged outputs/receipts request a normal private rebuild.
        pass
    if directory.exists():
        shutil.rmtree(directory)
    directory.mkdir(parents=True)
    lib = directory / 'lib/lean'
    src = directory / 'src'
    for relative in descriptor['base_inputs']:
        copy_material(base / relative, directory / relative)
    for name in SOURCES:
        target = src / 'src' / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(base / 'src/lean' / name, target)
    subprocess.run(['patch', '--batch', '--fuzz=0', '-p1', '-i', str(HERE / 'compiler-origin.patch')],
        cwd=src, check=True, stdout=sys.stderr)
    origin = (HERE / 'CompanionOrigin.lean').read_text()
    if origin.count('@COMPILER_ORIGIN_HASH@') != 1:
        raise ValueError('compiler identity handoff placeholder mismatch')
    (src / 'src/Lean/CompanionOrigin.lean').write_text(
        origin.replace('@COMPILER_ORIGIN_HASH@', REVISION + '-origin-' + identity))
    shutil.copy2(HERE / 'Frontend.lean', src / 'src/Frontend.lean')
    mods = ['Lean/CompanionOrigin', *[p[:-5] for p in SOURCES], 'Frontend']
    env = dict(os.environ, LEAN_PATH=str(lib), LEAN_SYSROOT=str(base))
    env.pop('LEAN_CC', None)  # Always use the content-bound bundled compiler.
    objects = []
    for mod in mods:
        target = lib / mod
        target.parent.mkdir(parents=True, exist_ok=True)
        for suffix in ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig', '.ilean'):
            Path(str(target) + suffix).unlink(missing_ok=True)
        subprocess.run([str(base / 'bin/lean'), '-o', str(target) + '.olean',
            '-c', str(target) + '.c', str(src / 'src' / (mod + '.lean'))],
            cwd=src / 'src', env=env, check=True, stdout=sys.stderr)
        obj = str(target) + '.o'
        subprocess.run([str(base / 'bin/leanc'), '-O1', *(['-DLEAN_EXPORTING'] if mod != 'Frontend' else []),
            '-c', str(target) + '.c', '-o', obj],
            env=env, check=True, stdout=sys.stderr)
        objects.append(obj)
    patch_native_archive(base, directory, objects[:-1])
    export = '-Wl,-export_dynamic' if sys.platform == 'darwin' else '-Wl,--export-dynamic'
    subprocess.run([str(base / 'bin/leanc'), export, '-o', str(directory / 'bin/frontend'), *objects],
        env=env, check=True, stdout=sys.stderr)
    (directory / 'driver.json').write_bytes(canonical(dict(base=str(base), lean=str(base / 'bin/lean'),
        leanc=str(base / 'bin/leanc'),
        objects=[Path(p).relative_to(directory).as_posix() for p in objects[:-1]],
        origin=REVISION + '-origin-' + identity)))
    for name in ('lean', 'leanc'):
        path = directory / 'bin' / name
        path.unlink()
        driver = HERE.joinpath('driver.py').read_text().split('\n', 1)[1]
        path.write_text('#!' + sys.executable + '\n' + driver)
        path.chmod(0o755)
    (directory / 'descriptor.json').write_bytes(canonical(descriptor))
    # Validate all selected outputs, including stock inputs and native objects,
    # before reuse. A damaged output rebuilds; missing origin is never inferred.
    artifacts = {p.relative_to(directory).as_posix(): dict(sha256=sha(p), mode=stat.S_IMODE(p.stat().st_mode))
                 for p in sorted(directory.rglob('*')) if p.is_file()}
    if inputs(root)[2] != identity:
        raise ValueError('compiler inputs changed during build')
    temporary_receipt = receipt.with_suffix('.json.tmp')
    temporary_receipt.write_bytes(canonical(artifacts))
    temporary_receipt.replace(receipt)
    return directory


def ensure(root):
    base, descriptor, identity = inputs(root)
    parent = root / 'build/compiler-origin'
    parent.mkdir(parents=True, exist_ok=True)
    with (parent / 'build.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        return build(root, base, descriptor, identity), identity


def environment(directory, identity):
    return dict(os.environ, LEAN_SYSROOT=str(directory), LAKE_OVERRIDE_LEAN='true',
        LEAN_GITHASH=REVISION, LEAN_COMPILER_ORIGIN=REVISION + '-origin-' + identity,
        PATH=str(directory / 'bin') + os.pathsep + os.environ['PATH'])


def main():
    root = HERE.parents[2]
    if sys.argv[1:] == ['ensure']:
        directory, identity = ensure(root)
        print(json.dumps(dict(directory=str(directory), identity=identity)))
    elif sys.argv[1:2] == ['stage'] and len(sys.argv) == 3:
        directory, identity = stage(root, sys.argv[2])
        print(json.dumps(dict(directory=str(directory), identity=identity)))
    elif sys.argv[1:2] == ['restore'] and len(sys.argv) == 3:
        directory, identity = restore(root, sys.argv[2])
        print(json.dumps(dict(directory=str(directory), identity=identity)))
    elif sys.argv[1:2] == ['run'] and len(sys.argv) > 2:
        directory, identity = ensure(root)
        command = sys.argv[2:]
        # The installed Lake runtime is untouched; it uses the explicit local
        # compiler via its supported override contract.
        os.execvpe(command[0], command, environment(directory, identity))
    else:
        raise SystemExit('expected ensure | stage DIRECTORY | restore DIRECTORY | run COMMAND [ARG ...]')


if __name__ == '__main__':
    main()
