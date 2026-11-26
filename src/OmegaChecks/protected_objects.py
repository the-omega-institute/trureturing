"""Compare both compiled OmegaMath interfaces with the source at a protected Git revision."""
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile

import protected_uses
from portable import backend_plan
from strict_lake import ROOT


def publication_modules(repository):
    source = repository / "src"
    paths = [source / "OmegaMath.lean", *(source / "OmegaMath").rglob("*.lean")]
    return sorted(".".join(path.relative_to(source).with_suffix("").parts)
                  for path in paths if path.is_file())


def compiled_path(repository, modules, strict):
    environment = {k: v for k, v in os.environ.items() if k not in {"LEAN_PATH", "LEAN_SRC_PATH"}}
    lake = ["lake"]
    if strict:
        # The archived revision supplies its own foundation overlay. Its scheduling
        # wrapper needs a Git checkout, while Lake can build these exact roots directly.
        config = subprocess.check_output(
            [sys.executable, "-I", "-B", "-c",
             "import runpy; print(runpy.run_path('src/OmegaChecks/strict_lake.py')['strict_config']())"],
            cwd=repository, env=environment, text=True).strip()
        lake.extend(["-f", config])
    if modules:
        subprocess.run([*lake, "build", *("+" + name for name in modules)], cwd=repository,
                       env=environment, check=True)
    value = subprocess.check_output([*lake, "env", "printenv", "LEAN_PATH"], cwd=repository,
                                    env=environment, text=True).strip()
    return os.pathsep.join(str((repository / entry).resolve()) for entry in value.split(os.pathsep))


def strict_witnesses(official_path, names):
    excluded = backend_plan(official_path, names)["mathlibOnly"]
    return [name for name in names if name not in excluded]


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
        old_d5, new_d5, omega_d5, legacy_owners, all_owners = protected_uses.targets(commit, before)
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
        protected_official = compiled_path(before, [*original, *old_d5], False)
        official_roots = set(modules) | set(legacy_owners) | set(new_d5)
        if omega_d5:
            official_roots.add("OmegaMathlib")
        candidate_official = compiled_path(ROOT, sorted(official_roots), False)
        protected_uses.compare(before, old_d5, new_d5, protected_official, candidate_official, omega_d5)

        def compare_objects(strict, protected_path, candidate_path, owners):
            label = "strict" if strict else "official"
            print(f"Comparing {label} OmegaMath declarations against {commit}", flush=True)
            command = [audit, "--protected-objects", protected_path, candidate_path,
                       *original, "--", *modules, "--legacy"]
            result = subprocess.run([*command, *owners], cwd=ROOT, stderr=subprocess.PIPE, text=True)
            if result.returncode and (
                    "missing observable D5 representation" in result.stderr or
                    "missing all-input correspondence in D5" in result.stderr):
                # A frozen owner outside the changed set can already contain the required witness.
                additional = sorted(set(all_owners) - set(legacy_owners))
                if additional:
                    compiled_path(ROOT, additional, False)
                    if strict:
                        additional = strict_witnesses(candidate_official, additional)
                        compiled_path(ROOT, additional, True)
                if additional:
                    subprocess.run([*command, *owners, *additional], cwd=ROOT, check=True)
                    return
            sys.stderr.write(result.stderr)
            result.check_returncode()

        compare_objects(False, protected_official, candidate_official, legacy_owners)
        # A restricted publication is invalid even when its source compiles in strict mode.
        backend_plan(protected_official, original)
        backend_plan(candidate_official, modules)
        strict_owners = strict_witnesses(candidate_official, legacy_owners)
        protected_strict = compiled_path(before, original, True)
        candidate_strict = compiled_path(ROOT, sorted(set(modules) | set(strict_owners)), True)
        compare_objects(True, protected_strict, candidate_strict, strict_owners)
