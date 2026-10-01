"""CI unit resolution against synthetic registrations, without workflow parsing."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


class CiUnitsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ci units ")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.script = self.root / "tools/scripts/workflow/ci_units.py"
        self.script.parent.mkdir(parents=True)
        shutil.copyfile(Path(__file__).with_name("ci_units.py"), self.script)
        (self.root / "Meta").mkdir()
        workflow = self.root / ".github/workflows/ci-fixture.yml"
        workflow.parent.mkdir(parents=True)
        workflow.write_text("opaque synthetic workflow\n")
        self.projects = {"version": 1, "projects": [
            {"path": "tests/T/T.csproj", "role": "owned-test",
             "include": ["linked/**/*.cs", "tests/T/**/*.cs"],
             "exclude": ["linked/Excluded.cs"], "references": ["src/P/P.csproj"]},
            {"path": "src/P/P.csproj", "role": "production",
             "include": ["src/P/**/Nested/**/*.cs"], "exclude": [],
             "references": ["src/D/D.csproj"]},
            {"path": "src/D/D.csproj", "role": "production",
             "include": ["shared/Exact.cs"], "exclude": [], "references": []},
        ]}
        self.manifest = {"schema": "ci-units-v1", "shared_inputs": ["global.json"],
                         "units": [self.unit()]}

    @staticmethod
    def unit():
        return {"id": "fixture", "workflow": ".github/workflows/ci-fixture.yml",
                "project": "tests/T/T.csproj", "test": True, "lean": "toolchain",
                "dotnet": True, "inputs": ["!linked/Omit.cs", "assets/*", "global.json"]}

    def resolve(self, unit="fixture", manifest_text=None):
        (self.root / "Meta/engineering-projects.json").write_text(json.dumps(self.projects))
        (self.root / "Meta/ci-units.json").write_text(
            json.dumps(self.manifest) if manifest_text is None else manifest_text)
        self.paths = self.root / "hit paths"
        return subprocess.run([sys.executable, str(self.script), "resolve", unit,
                               "--paths-file", str(self.paths)], cwd=tempfile.gettempdir(),
                              capture_output=True, text=True)

    def assert_error(self, result, message):
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn(message, result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertFalse(self.paths.exists())

    def test_unknown_unit(self):
        self.assert_error(self.resolve("unknown"), "unknown unit")

    def test_invalid_manifest(self):
        mutations = [
            (lambda m: m.update(schema="other"), "schema"),
            (lambda m: m.update(extra=True), "keys"),
            (lambda m: m["units"].append(copy.deepcopy(m["units"][0])), "duplicate"),
            (lambda m: m["units"][0].update(project=None), "project"),
            (lambda m: m["units"][0].update(project="missing/M.csproj"), "unregistered"),
            (lambda m: m["units"][0].update(project="src/P/P.csproj"), "test role"),
            (lambda m: m["units"][0].update(workflow=".github/workflows/missing.yml"), "workflow"),
            (lambda m: m["units"][0].update(workflow="../escape.yml"), "workflow"),
            (lambda m: m["units"][0].update(inputs=[""]), "pattern"),
            (lambda m: m["units"][0].update(inputs=["!"]), "pattern"),
            (lambda m: m["units"][0].update(inputs=["x\ny"]), "pattern"),
            (lambda m: m["units"][0].update(inputs=["a", "a"]), "duplicate"),
            (lambda m: m["units"][0].update(inputs=["z", "a"]), "sorted"),
            (lambda m: m["units"][0].update(test="true"), "test"),
            (lambda m: m["units"][0].update(dotnet=1), "dotnet"),
            (lambda m: m["units"][0].update(lean="invalid"), "lean"),
            (lambda m: m["units"][0].update(id="bad\nid"), "id"),
            (lambda m: m["units"][0].update(command="echo nope"), "keys"),
            (lambda m: m.update(shared_inputs=None), "patterns"),
            (lambda m: m.update(units={}), "units"),
        ]
        original = copy.deepcopy(self.manifest)
        for mutate, message in mutations:
            with self.subTest(message=message, mutate=mutate):
                self.manifest = copy.deepcopy(original)
                mutate(self.manifest)
                self.assert_error(self.resolve(), message)

    def test_duplicate_json_key_and_malformed_json(self):
        self.assert_error(self.resolve(manifest_text='{"schema":"ci-units-v1","schema":"ci-units-v1"}'), "duplicate")
        self.assert_error(self.resolve(manifest_text="{"), "JSON")

    def test_unregistered_reference_and_cycle(self):
        self.projects["projects"][2]["references"] = ["missing.csproj"]
        self.assert_error(self.resolve(), "unregistered")
        self.projects["projects"][2]["references"] = ["tests/T/T.csproj"]
        self.assert_error(self.resolve(), "cyclic")

    def test_invalid_project_registry(self):
        mutations = [
            (lambda p: p.update(version=2), "version"),
            (lambda p: p["projects"].append(copy.deepcopy(p["projects"][0])), "duplicate"),
            (lambda p: p["projects"][0].update(include=[""]), "pattern"),
            (lambda p: p["projects"][0].update(include=["!source.cs"]), "include"),
            (lambda p: p["projects"][0].update(references=None), "references"),
            (lambda p: p["projects"][0].update(path="../T.csproj"), "project"),
        ]
        original = copy.deepcopy(self.projects)
        for mutate, message in mutations:
            with self.subTest(message=message):
                self.projects = copy.deepcopy(original)
                mutate(self.projects)
                self.assert_error(self.resolve(), message)

    def test_validates_other_units_too(self):
        other = self.unit()
        other.update(id="z-other", project=None)
        self.manifest["units"].append(other)
        self.assert_error(self.resolve(), "project")

    def test_units_must_be_sorted(self):
        other = self.unit()
        other["id"] = "a-other"
        self.manifest["units"].append(other)
        self.assert_error(self.resolve(), "sorted")

    def test_resolves_transitive_inputs_and_does_not_apply_exclude(self):
        result = self.resolve()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "project=tests/T/T.csproj\ntest=true\nlean=toolchain\ndotnet=true\n")
        self.assertEqual(self.paths.read_text().splitlines(), [
            ".github/workflows/ci-fixture.yml", "assets/*", "global.json",
            "linked/*.cs", "shared/Exact.cs", "src/D/D.csproj", "src/D/packages.lock.json",
            "src/P/*Nested/*.cs", "src/P/P.csproj", "src/P/packages.lock.json",
            "tests/T/*.cs", "tests/T/T.csproj", "tests/T/packages.lock.json", "!linked/Omit.cs",
        ])

    def test_non_test_without_project_and_all_lean_modes(self):
        for lean in ("none", "toolchain", "build"):
            with self.subTest(lean=lean):
                self.manifest["units"][0].update(test=False, project=None, lean=lean, dotnet=False)
                result = self.resolve()
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout, f"project=\ntest=false\nlean={lean}\ndotnet=false\n")
                self.assertEqual(self.paths.read_text().splitlines(), [
                    ".github/workflows/ci-fixture.yml", "assets/*", "global.json", "!linked/Omit.cs"])

    def test_non_test_can_register_production_project(self):
        self.manifest["units"][0].update(test=False, project="src/P/P.csproj")
        result = self.resolve()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("shared/Exact.cs", self.paths.read_text().splitlines())

    def test_diamond_references_are_deduplicated(self):
        self.projects["projects"][0]["references"].append("src/D/D.csproj")
        result = self.resolve()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.paths.read_text().splitlines().count("shared/Exact.cs"), 1)


if __name__ == "__main__":
    unittest.main()
