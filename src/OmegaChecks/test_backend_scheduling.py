"""Exercise the production Lake scheduler with cold and changing module artifacts."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from strict_lake import ROOT


class BackendScheduling(unittest.TestCase):
    def test_no_build_checks_cold_warm_and_stale_artifacts(self):
        with tempfile.TemporaryDirectory(prefix="omega-no-build-") as directory:
            project = Path(directory)
            for filename in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                shutil.copyfile(ROOT / filename, project / filename)
            shutil.copytree(ROOT / "src/OmegaBuild", project / "src/OmegaBuild")
            scripts = project / "src/OmegaChecks"
            scripts.mkdir()
            for source in (ROOT / "src/OmegaChecks").glob("*.py"):
                shutil.copyfile(source, scripts / source.name)
            (project / ".lake").mkdir()
            (project / ".lake/packages").symlink_to((ROOT / ".lake/packages").resolve(), target_is_directory=True)
            (project / "D5").mkdir()
            marked = project / "D5/Marked.lean"
            marked.write_text("import OmegaBuild.Commands\ncompile_only_with_mathlib\ndef answer := 42\n")
            (project / "D5/Plain.lean").write_text("def plain := 7\n")
            subprocess.run(["git", "init", "--quiet"], cwd=project, check=True)
            wrapper = [sys.executable, "-B", "src/OmegaChecks/strict_lake.py"]
            def run(args, expected):
                result = subprocess.run(args, cwd=project, capture_output=True, text=True)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)

            build = project / ".lake/build"
            official = build / "lib/lean/D5/Marked.olean"
            planner = build / "bin/omegaBackendPlan"
            strict = build / "omega-strict/lib/lean/D5"
            run(["lake", "build", "--no-build", "+D5.Marked"], 3)
            run([*wrapper, "build", "--no-build", "+D5.Marked"], 3)
            self.assertFalse(official.exists())
            self.assertFalse(planner.exists())
            run(["lake", "build", "+D5.Marked"], 0)
            stamp = official.stat().st_mtime_ns
            run([*wrapper, "--no-build", "build", "+D5.Marked"], 3)
            self.assertFalse(planner.exists())
            run(["lake", "build", "omegaBackendPlan"], 0)
            run([*wrapper, "build", "--no-build", "+D5.Marked"], 0)
            run([*wrapper, "build", "--no-build", "+D5.Marked:c.o"], 3)
            self.assertEqual(stamp, official.stat().st_mtime_ns)
            self.assertFalse((strict / "Marked.olean").exists())
            run([*wrapper, "build", "--no-build", "+D5.Plain"], 3)
            self.assertFalse((strict / "Plain.olean").exists())
            run([*wrapper, "build", "+D5.Plain"], 0)
            run([*wrapper, "build", "--no-build", "+D5.Plain"], 0)
            marked.write_text(marked.read_text().replace("42", "43"))
            run([*wrapper, "build", "--no-build", "+D5.Marked"], 3)
            self.assertEqual(stamp, official.stat().st_mtime_ns)

    def test_marker_changes_and_transitive_targets(self):
        with tempfile.TemporaryDirectory(prefix="omega-scheduling-") as directory:
            project = Path(directory)
            for filename in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                shutil.copyfile(ROOT / filename, project / filename)
            for name in ("src", "strict"):
                shutil.copytree(ROOT / name, project / name)
            # Keep the protected publication in this fixture to the branches used by its clients.
            shutil.rmtree(project / "src/OmegaMath")
            (project / "src/OmegaMath/Data").mkdir(parents=True)
            for source in ("Nat", "Ratio", "Int"):
                relative = Path(f"src/OmegaMath/Data/{source}.lean")
                shutil.copyfile(ROOT / relative, project / relative)
            (project / "src/OmegaMath.lean").write_text("module\nprelude\npublic import OmegaMath.Data.Int\n")
            subprocess.run(["git", "init", "--quiet"], cwd=project, check=True)
            (project / ".lake").mkdir()
            (project / ".lake/packages").symlink_to((ROOT / ".lake/packages").resolve(), target_is_directory=True)
            directory = project / "D5"
            directory.mkdir()
            (directory / "A.lean").write_text("import OmegaMath.Data.Nat\n")
            (project / "Trureturing.lean").write_text("import D5.A\n")
            subprocess.run(["git", "add", "src", "strict", "D5", "Trureturing.lean", "lean-toolchain",
                            "lakefile.toml", "lake-manifest.json"], cwd=project, check=True)
            subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                            "commit", "--quiet", "--no-gpg-sign", "-m", "Protected fixture"], cwd=project, check=True)
            subprocess.run(["git", "update-ref", "refs/remotes/origin/dev", "HEAD"], cwd=project, check=True)
            (directory / "C.lean").write_text("import D5.B\n")
            (directory / "D.lean").write_text("import D5.A\n")
            (directory / "All.lean").write_text("import D5.C\nimport D5.D\n")
            b = directory / "B.lean"
            header = "import D5.A\nimport OmegaBuild.Commands\nimport Mathlib.Data.Nat.Factorial.Basic\n"
            marker = "compile_only_with_mathlib\n"
            use_factorial = "def answer (n : Omega.Nat) : Nat := Nat.factorial n\n"
            b.write_text(header + marker + use_factorial)
            (project / "Trureturing.lean").write_text("import D5.All\n")
            (project / "src/OmegaChecks/ReviewBridge.lean").write_text(
                "import Trureturing\nexample (n : Nat) : answer n = Nat.factorial n := rfl\n")

            supplemental = "OmegaChecks.Portable.MathlibFactorial"
            scope = {"shared": [], "library": [], "basis": [], "common": [supplemental], "consumers": ["D5.All"]}
            scope_file = project / "scope.json"
            scope_file.write_text(json.dumps(scope))
            def check(expected_error=None):
                result = subprocess.run([sys.executable, "-B", "src/OmegaChecks/check.py", "--scope", scope_file],
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

            # Every supported entry must also build the portable sibling from a cold overlay.
            for cmd in (["lake", "test", "--", "OmegaChecks.ReviewBridge"],
                        [sys.executable, "src/OmegaChecks/strict_lake.py", "build", "+Trureturing",
                         "@trureturing/+D5.B:olean", "D5/C.lean:olean"],
                        [sys.executable, "src/OmegaChecks/strict_lake.py", "build"]):
                shutil.rmtree(strict_artifacts.parent.parent.parent)
                result = subprocess.run(cmd, cwd=project, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual({p.stem for p in strict_artifacts.glob("*.olean")}, {"A", "D"})
                for skipped in ("Trureturing.olean", "OmegaChecks/ReviewBridge.olean"):
                    self.assertFalse((strict_artifacts.parent / skipped).exists())

            # A previous official success must not bypass the next strict build.
            b.write_text(header + "def answer (n : Omega.Nat) : Nat := Nat.succ n\n")
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
