"""Derive an ordinary import view of the isolated OmegaInit artifacts."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
GENERATOR = Path(__file__).with_name("InitPort") / "Hosted.lean"
FOUNDATIONS = ("OmegaInit", "OmegaMathlib", "OmegaMath")
PARTS = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig", ".ilean")


def foundation_files(source, module=None):
    modules = (module,) if module else FOUNDATIONS
    paths = [path for name in modules for path in [*source.glob(name + ".*"), *(source / name).rglob("*")]]
    return sorted(path for path in paths if path.is_file() and path.name.endswith(PARTS))


def link_other_roots(source, target):
    if source.is_dir():
        for path in source.iterdir():
            if path.name.split(".")[0] not in FOUNDATIONS:
                try:
                    (target / path.name).symlink_to(os.path.relpath(path, target))
                except FileExistsError:
                    pass


def make_view(source, target, files, *, snapshot=False):
    target.mkdir(parents=True, exist_ok=True)
    owners = [".".join(path.relative_to(source).with_suffix("").parts) for path in files if path.suffix == ".olean"]
    if owners:
        subprocess.run(["lake", "build", "+OmegaChecks.InitPort.HostedProjection"],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
        subprocess.run(["lake", "env", "lean", "--run", GENERATOR, source, target, *owners], cwd=ROOT, check=True)
    # Lean resolves a whole module prefix in one directory. The projector writes
    # the changed owners. Keep all other parts of that same foundation available.
    for path in files:
        dest = target / path.relative_to(source)
        if not dest.exists():
            dest.parent.mkdir(parents=True, exist_ok=True)
            if snapshot:
                shutil.copyfile(path, dest)
            else:
                dest.symlink_to(os.path.relpath(path, dest.parent))


def fingerprint(source, files):
    digest = hashlib.sha256(GENERATOR.read_bytes())
    digest.update((ROOT / "lean-toolchain").read_bytes())
    for tool in ("InitPort/HostedProjection.lean", "InitPort/HostedBitwise.lean",
                 "InitCompiler/CompilerMarkers.lean", "Interface.lean", "Interface/Equations.lean"):
        digest.update((GENERATOR.parents[1] / tool).read_bytes())
    for path in files:
        digest.update(os.fsencode(path.relative_to(source)) + b"\0")
        with path.open("rb") as stream:
            digest.update(hashlib.file_digest(stream, "sha256").digest())
    return digest.hexdigest()


def cached_view(source):
    cache = ROOT / ".lake/omega-hosted"
    cache.mkdir(parents=True, exist_ok=True)
    while True:
        files = foundation_files(source)
        key = fingerprint(source, files)
        target = cache / key
        if target.is_dir():
            break
        with tempfile.TemporaryDirectory(dir=cache) as temporary:
            view = Path(temporary)
            make_view(source, view, files, snapshot=True)
            if fingerprint(source, foundation_files(source)) != key:
                continue
            try:
                view.rename(target)
            except OSError:
                if not target.is_dir():
                    raise
            break
    link_other_roots(source, target)
    return target
