"""Exercise the public backend command through a dependency in an external Lake workspace."""
import json
import shutil
import sys
from pathlib import Path
import subprocess
import tempfile

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
        assert report["mathlibOnly"] == {"UseFactorial": ["UseFactorial", "FactorialLibrary"]}, report
        assert {"name": "usesChoice", "module": "UseFactorial", "axioms": ["Classical.choice"]} in report["declarations"]


def test_publication_facades():
    subprocess.run(["lake", "build", "omegaAudit"], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="omega-facades-") as directory:
        project = Path(directory)
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            shutil.copyfile(ROOT / name, project / name)
        (project / ".lake").mkdir()
        (project / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)
        shutil.copytree(ROOT / "src/OmegaBuild", project / "src/OmegaBuild")
        checks = project / "src/OmegaChecks"
        checks.mkdir()
        for name in ("check.py", "portable.py", "scope.py", "strict_lake.py"):
            shutil.copyfile(ROOT / "src/OmegaChecks" / name, checks / name)
        (checks / "InitCompiler.lean").write_text("import Lean\n")
        subprocess.run(["git", "init", "--quiet"], cwd=project, check=True)

        def write(folder, module, content):
            path = project.joinpath(folder, *module.split(".")).with_suffix(".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("module\n" + content)

        marked = "OmegaChecks.Marked"
        direct = "OmegaInit.Direct"
        inherited = "OmegaMathlib.Inherited"
        consumer = "OmegaMath.Inherited"
        marker = "import OmegaBuild.Commands\ncompile_only_with_mathlib\n"
        write("src", marked, marker)
        write("src", direct, marker)
        write("src", inherited, f"import {marked}\n")
        write("src", consumer, f"prelude\nimport {inherited}\n")
        for facade in (direct, inherited):
            write("strict", facade, "prelude\n")
        audit = ROOT / ".lake/build/bin/omegaAudit"
        strict_build = [sys.executable, "-B", checks / "strict_lake.py", "build"]
        library = [sys.executable, "-B", "-c",
                   "import sys; sys.path.insert(0, 'src/OmegaChecks'); import check; "
                   "check.ENV.update(check.lake_environment()); check.check_library(sys.argv[1:])"]
        for command, expected in [([*strict_build, "+" + direct], direct),
                                  ([*library, inherited], f"{inherited} -> {marked}"),
                                  ([*strict_build, "+" + consumer], f"{inherited} -> {marked}")]:
            result = subprocess.run(command, cwd=project, text=True, capture_output=True)
            assert result.returncode and "Omega publication requires both backends" in result.stderr, result
            assert expected in result.stderr, result
        official = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=project, text=True).strip()
        for module in (direct, inherited, consumer):
            result = subprocess.run([audit, "--publication-layers", official, module], cwd=project,
                                    text=True, capture_output=True)
            assert result.returncode and "Omega publication requires both backends" in result.stderr, result

        write("src", marked, "import OmegaBuild.Commands\n")
        subprocess.run([*strict_build, "+" + consumer], cwd=project, check=True)
        subprocess.run([audit, "--publication-layers", official, consumer], cwd=project, check=True)


if __name__ == "__main__":
    test_external_package()
    test_publication_facades()
