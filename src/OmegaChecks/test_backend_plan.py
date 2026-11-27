"""Exercise the public backend command through a dependency in an external Lake workspace."""
import json
from pathlib import Path
import subprocess
import tempfile

from portable import backend_plan
from strict_lake import ROOT


def package(directory, name, dependency, modules):
    directory.mkdir()
    dependency_name, dependency_dir = dependency
    manifest = json.loads((dependency_dir / "lake-manifest.json").read_text())
    packages = str(ROOT / ".lake/packages")
    (directory / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
    (directory / "lakefile.toml").write_text(
        f'name = "{name}"\ndefaultTargets = ["{name}"]\npackagesDir = {json.dumps(packages)}\n'
        f'[[require]]\nname = "{dependency_name}"\npath = {json.dumps(str(dependency_dir))}\n'
        f'[[lean_lib]]\nname = "{name}"\nroots = {json.dumps(list(modules))}\n')
    for entry in manifest["packages"]:
        entry["inherited"] = True
    manifest["packages"].insert(0, {
        "type": "path", "scope": "", "name": dependency_name, "dir": str(dependency_dir),
        "inherited": False, "manifestFile": "lake-manifest.json", "configFile": "lakefile.toml",
    })
    manifest.update(name=name, packagesDir=packages)
    (directory / "lake-manifest.json").write_text(json.dumps(manifest))
    for module, source in modules.items():
        (directory / f"{module}.lean").write_text(source)


def test_external_package():
    subprocess.run(["lake", "build", "omegaBackendPlan"], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="omega-backend-packages-") as directory:
        library = Path(directory) / "library"
        client = Path(directory) / "client"
        package(library, "factorialLibrary", ("trureturing", ROOT), {
            "FactorialLibrary": """module
public import OmegaBuild.Commands
public import OmegaMath.Data.Nat
public import Mathlib.Data.Nat.Factorial.Basic

compile_only_with_mathlib

public def fact (n : Omega.Nat) : Nat := Nat.factorial n
""",
        })
        package(client, "consumer", ("factorialLibrary", library), {
            "UseFactorial": """import FactorialLibrary

example (n : Nat) : fact n = Nat.factorial n := rfl
theorem usesChoice : True := Classical.choice ⟨True.intro⟩
""",
            "UseSquare": """prelude
import OmegaMath.Data.Nat

example (a k : Omega.Nat) : Omega.Eq ((a.mul k).mul (a.mul k)) ((a.mul a).mul (k.mul k)) :=
  Omega.Nat.square_mul a k
""",
        })
        subprocess.run(["lake", "build"], cwd=client, check=True)
        outputs = [directory / ".lake/build/lib/lean" / f"{name}.olean" for directory, name in [
            (library, "FactorialLibrary"), (client, "UseFactorial"), (client, "UseSquare"),
        ]]
        timestamps = [path.stat().st_mtime_ns for path in outputs]
        subprocess.run(["lake", "build"], cwd=client, check=True)
        assert timestamps == [path.stat().st_mtime_ns for path in outputs], "warm Lake build recompiled an input"
        search = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=client, text=True).strip()
        report = json.loads(subprocess.check_output([
            ROOT / ".lake/build/bin/omegaBackendPlan", search, "UseFactorial", "UseSquare",
        ], cwd=client, text=True))
        assert backend_plan(search, ["UseFactorial", "UseSquare"], prepared=True) == report
        assert report["mathlibOnly"] == {"UseFactorial": ["UseFactorial", "FactorialLibrary"]}, report
        assert {"name": "usesChoice", "module": "UseFactorial", "axioms": ["Classical.choice"]} in report["declarations"]


if __name__ == "__main__":
    test_external_package()
