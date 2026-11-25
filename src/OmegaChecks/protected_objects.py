"""Compare both compiled OmegaMath interfaces with the source at a protected Git revision."""
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile

import protected_uses
from strict_lake import ROOT


def publication_modules(repository):
    source = repository / "src"
    paths = [source / "OmegaMath.lean", *(source / "OmegaMath").rglob("*.lean")]
    return sorted(".".join(path.relative_to(source).with_suffix("").parts)
                  for path in paths if path.is_file())


def compiled_path(repository, modules, strict):
    lake = ([sys.executable, "-I", "-B", "src/OmegaChecks/strict_lake.py"] if strict else ["lake"])
    environment = {k: v for k, v in os.environ.items() if k not in {"LEAN_PATH", "LEAN_SRC_PATH"}}
    if modules:
        subprocess.run([*lake, "build", *("+" + name for name in modules)], cwd=repository,
                       env=environment, check=True)
    value = subprocess.check_output([*lake, "env", "printenv", "LEAN_PATH"], cwd=repository,
                                    env=environment, text=True).strip()
    return os.pathsep.join(str((repository / entry).resolve()) for entry in value.split(os.pathsep))


def check(base):
    commit = subprocess.check_output(["git", "rev-parse", "--verify", "--end-of-options", base + "^{commit}"],
                                     cwd=ROOT, text=True).strip()
    modules = publication_modules(ROOT)
    with tempfile.TemporaryDirectory(prefix="omega-protected-") as temporary:
        before = Path(temporary)
        inputs = ["src", "strict", "D5", "Trureturing.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]
        with subprocess.Popen(["git", "archive", commit, "--", *inputs], cwd=ROOT, stdout=subprocess.PIPE) as proc:
            with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
                archive.extractall(before, filter="data")
            if proc.wait():
                raise RuntimeError(f"failed to extract the protected Omega sources at {commit}")
        old_d5, new_d5 = protected_uses.targets(commit, before)
        original = publication_modules(before)
        missing = sorted(set(original) - set(modules))
        if missing:
            raise ValueError(f"removed protected public import paths: {', '.join(missing)}")
        if all((before / name).read_bytes() == (ROOT / name).read_bytes()
               for name in ("lean-toolchain", "lake-manifest.json")):
            (before / ".lake").mkdir()
            (before / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)
        subprocess.run(["lake", "build", "omegaAudit"], cwd=ROOT, check=True)
        audit = ROOT / ".lake/build/bin/omegaAudit"
        for strict in (False, True):
            protected_path = compiled_path(before, original if strict else [*original, *old_d5], strict)
            candidate_path = compiled_path(ROOT, modules if strict else [*modules, *new_d5], strict)
            if not strict:
                protected_uses.compare(before, old_d5, new_d5, protected_path, candidate_path)
            label = "strict" if strict else "official"
            print(f"Comparing {label} OmegaMath declarations against {commit}", flush=True)
            subprocess.run([audit, "--protected-objects", protected_path, candidate_path,
                            *original, "--", *modules], cwd=ROOT, check=True)
