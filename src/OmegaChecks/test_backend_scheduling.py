"""Exercise the production Lake scheduler with cold and changing module artifacts."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest
from unittest.mock import Mock, patch

import host_lake
from host_lake import ROOT, UPSTREAM


class BackendScheduling(unittest.TestCase):
    def test_foundation_overlays_resolve_the_init_compiler_relative_to_the_reference_workspace(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            package = root / "packages/omegamath"
            reference = package / "checks/mathlib"
            overlay = root / "foundation.toml"
            foundation = Mock()
            foundation.strict_config.return_value = overlay
            foundation.foundation_config.return_value = overlay
            with patch.multiple(host_lake, ROOT=root, REFERENCE=reference), \
                 patch.object(host_lake, "foundation", return_value=foundation):
                for label, basis in (("strict", package / "strict"), ("common", root / "common")):
                    with self.subTest(label=label):
                        overlay.write_text(
                            'name = "omegamath"\n'
                            '[[lean_lib]]\nname = "OmegaInit"\n'
                            f'srcDir = {json.dumps(str(basis))}\n'
                            '[[lean_lib]]\nname = "OmegaChecks.InitCompiler"\nsrcDir = "../../src"\n')
                        config = host_lake.package_overlay(f".lake/build/omega-{label}", label,
                                                           basis if label == "common" else None)
                        libraries = tomllib.loads(config.read_text())["lean_lib"]
                        self.assertEqual([Path(lib["srcDir"]) for lib in libraries],
                                         [basis, package / "src"])

    def test_reference_package_paths_are_relative_to_its_own_workspace(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            package = root / "packages/omegamath"
            reference = package / "checks/mathlib"
            reference.mkdir(parents=True)
            (package / "lakefile.toml").write_text('name = "omegamath"\n')
            (reference / "lakefile.toml").write_text(
                'name = "reference"\n'
                '[[lean_lib]]\nname = "OmegaMathlib"\nsrcDir = "src"\n'
                '[[lean_lib]]\nname = "OmegaMath"\nsrcDir = "../../src"\n'
                '[[lean_exe]]\nname = "omegaAudit"\nsrcDir = "../../src"\n')
            with patch.multiple(host_lake, ROOT=root, UPSTREAM=package, REFERENCE=reference):
                config = host_lake.package_overlay(".lake/build/omega-reference", "reference", None)
            data = tomllib.loads(config.read_text())
            self.assertEqual(data["name"], "omegamath")
            self.assertFalse(data["preferReleaseBuild"])
            self.assertEqual(Path(data["buildDir"]), package / ".lake/build/omega-reference")
            self.assertEqual([Path(lib["srcDir"]) for lib in data["lean_lib"]],
                             [reference / "src", package / "src"])
            self.assertEqual(Path(data["lean_exe"][0]["srcDir"]), package / "src")

    def test_ordinary_init_compiler_library_owns_its_helpers(self):
        plugin = "OmegaChecks.InitCompiler"
        with tempfile.TemporaryDirectory(prefix="omega-plugin-") as directory:
            project = Path(directory)
            shutil.copyfile(ROOT / "lean-toolchain", project / "lean-toolchain")
            prefix = Path("src/OmegaChecks")
            (project / prefix).mkdir(parents=True)
            shutil.copyfile(UPSTREAM / prefix / "InitCompiler.lean", project / prefix / "InitCompiler.lean")
            shutil.copytree(UPSTREAM / prefix / "InitCompiler", project / prefix / "InitCompiler")
            # Preserve both overlapping library selections and their order from this checkout.
            config = tomllib.loads((UPSTREAM / "lakefile.toml").read_text())
            selected = [lib for lib in config["lean_lib"] if lib["name"] in {"OmegaChecks", plugin}]
            self.assertEqual({lib["name"] for lib in selected}, {"OmegaChecks", plugin})
            source = 'name = ' + json.dumps(config['name']) + '\n'
            for library in selected:
                source += '\n[[lean_lib]]\n' + ''.join(
                    key + ' = ' + json.dumps(value) + '\n' for key, value in library.items())
            (project / "lakefile.toml").write_text(source)
            subprocess.run(["lake", "build", plugin + ":shared"], cwd=project, check=True)
            subprocess.run(["lake", "--no-build", "build", plugin + ":shared"], cwd=project, check=True)

    def test_marker_changes_and_transitive_targets(self):
        with tempfile.TemporaryDirectory(prefix="omega-scheduling-") as directory:
            project = Path(directory)
            for filename in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                shutil.copyfile(ROOT / filename, project / filename)
            checks = project / "src/OmegaChecks"
            checks.mkdir(parents=True)
            for filename in ("portable.py", "host_lake.py"):
                shutil.copyfile(ROOT / "src/OmegaChecks" / filename, checks / filename)
            subprocess.run(["git", "init", "--quiet"], cwd=project, check=True)
            (project / ".lake").mkdir()
            (project / ".lake/packages").symlink_to((ROOT / ".lake/packages").resolve(), target_is_directory=True)
            directory = project / "D5"
            directory.mkdir()
            (directory / "A.lean").write_text("import OmegaMath.Data.Nat\n")
            (directory / "C.lean").write_text("import D5.B\n")
            (directory / "D.lean").write_text("import D5.A\n")
            (directory / "All.lean").write_text("import D5.C\nimport D5.D\n")
            b = directory / "B.lean"
            header = "import D5.A\nimport OmegaBuild.Commands\nimport Mathlib.Data.Nat.Factorial.Basic\n"
            marker = "compile_only_with_mathlib\n"
            use_factorial = "def answer (n : Omega.Nat) : Nat := Nat.factorial n\n"
            b.write_text(header + marker + use_factorial)
            (project / "Trureturing.lean").write_text("import D5.All\n")
            (directory / "ReviewBridge.lean").write_text(
                "import Trureturing\nexample (n : Nat) : answer n = Nat.factorial n := rfl\n")

            supplemental = "OmegaChecks.Portable.MathlibFactorial"
            scope = {"shared": [], "library": [], "basis": [], "common": [supplemental, "D5.D"], "consumers": ["D5.All"]}
            def check(expected_error=None):
                script = ("import sys; sys.path.insert(0, 'src/OmegaChecks'); import portable; "
                          f"portable.check({scope['consumers']!r}, 'both', basis_roots={scope['basis']!r}, "
                          f"common_roots={scope['common']!r})")
                result = subprocess.run([sys.executable, "-B", "-c", script],
                                        cwd=project, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                if expected_error:
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn(expected_error, result.stdout, result.stdout)
                else:
                    self.assertEqual(result.returncode, 0, result.stdout)
            check()
            strict_artifacts = project / ".lake/build/omega-strict/lib/lean/D5"
            report_file = project / ".lake/build/omega-checks/selected-official-axioms.json"
            reported = json.loads(report_file.read_text())
            self.assertEqual(reported["mathlibOnly"], {"D5.B": ["D5.B"], "D5.C": ["D5.C", "D5.B"],
                                                        "D5.All": ["D5.All", "D5.C", "D5.B"]})
            self.assertIn("answer", [row["name"] for row in reported["declarations"]])
            self.assertNotIn(supplemental, reported["consumerModules"])
            self.assertNotIn(supplemental, {row["module"] for row in reported["declarations"]})
            self.assertEqual({p.stem for p in strict_artifacts.glob("*.olean")}, {"A", "D"})
            self.assertTrue((project / ".lake/build/omega-common/lib/lean/D5/D.olean").is_file())

            # Every supported entry must also build the portable sibling from a cold overlay.
            for cmd in ([sys.executable, "-B", "src/OmegaChecks/host_lake.py", "build", "+D5.ReviewBridge"],
                        [sys.executable, "-B", "src/OmegaChecks/host_lake.py", "build", "+Trureturing",
                         "@trureturing/+D5.B:olean", "D5/C.lean:olean"],
                        [sys.executable, "-B", "src/OmegaChecks/host_lake.py", "build"]):
                shutil.rmtree(strict_artifacts.parent.parent.parent)
                result = subprocess.run(cmd, cwd=project, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual({p.stem for p in strict_artifacts.glob("*.olean")}, {"A", "D"})
                for skipped in ("Trureturing.olean", "D5/ReviewBridge.olean"):
                    self.assertFalse((strict_artifacts.parent / skipped).exists())

            # A previous official success must not bypass the next strict build.
            b.write_text(header + use_factorial)
            check("Application type mismatch")
            # Repeat from a cold strict build directory.
            shutil.rmtree(project / ".lake/build/omega-strict")
            check("Application type mismatch")
            b.write_text(header + marker + "def answer : Nat := false\n")
            check("Type mismatch")
            b.write_text("import D5.A\ndef answer (n : Omega.Nat) : Omega.Nat := n\n")
            check()
            self.assertEqual(json.loads(report_file.read_text())["mathlibOnly"], {})
            self.assertEqual({p.stem for p in strict_artifacts.glob("*.olean")}, {"A", "B", "C", "D", "All"})


if __name__ == "__main__":
    unittest.main()
