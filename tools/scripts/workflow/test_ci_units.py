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
                         "closure_excludes": [], "units": [self.unit()],
                         "caches": {"fixture-build": {"project": "tests/T/T.csproj",
                                                      "inputs": ["config/*.props"]}}}

    @staticmethod
    def unit():
        return {"id": "fixture", "workflow": ".github/workflows/ci-fixture.yml",
                "project": "tests/T/T.csproj", "test": True, "lean": "toolchain",
                "dotnet": True, "inputs": ["!linked/Omit.cs", "assets/*", "global.json"]}

    def resolve(self, unit="fixture", manifest_text=None,
                workflow_ref="owner/repo/.github/workflows/ci-fixture.yml@refs/pull/7/merge"):
        (self.root / "Meta/engineering-projects.json").write_text(json.dumps(self.projects))
        (self.root / "Meta/ci-units.json").write_text(
            json.dumps(self.manifest) if manifest_text is None else manifest_text)
        self.paths = self.root / "hit paths"
        return subprocess.run([sys.executable, str(self.script), "resolve", unit,
                               "--paths-file", str(self.paths), "--workflow-ref", workflow_ref],
                              cwd=tempfile.gettempdir(),
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

    def test_closure_excludes_drop_registered_includes_under_a_prefix(self):
        self.manifest["closure_excludes"] = ["shared/"]
        result = self.resolve()
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = self.paths.read_text().splitlines()
        self.assertNotIn("shared/Exact.cs", lines)
        self.assertIn("src/D/D.csproj", lines)
        self.assertIn("src/P/*Nested/*.cs", lines)

    def test_closure_excludes_do_not_drop_explicit_unit_inputs(self):
        self.manifest["closure_excludes"] = ["shared/"]
        self.manifest["units"][0]["inputs"] = ["!linked/Omit.cs", "assets/*", "global.json", "shared/Exact.cs"]
        result = self.resolve()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("shared/Exact.cs", self.paths.read_text().splitlines())

    def test_invalid_closure_excludes(self):
        for value in ("shared/", ["shared"], [""], ["b/", "a/"], ["a/", "a/"], [1]):
            with self.subTest(value=value):
                self.manifest["closure_excludes"] = value
                self.assert_error(self.resolve(), "closure_excludes")

    def test_calling_workflow_must_own_the_unit(self):
        other = self.root / ".github/workflows/ci-other.yml"
        other.write_text("opaque synthetic workflow\n")
        self.assert_error(
            self.resolve(workflow_ref="owner/repo/.github/workflows/ci-other.yml@refs/heads/dev"),
            "does not own unit")

    def test_malformed_workflow_ref(self):
        for ref in ("", "owner/repo/.github/workflows/ci-fixture.yml",
                    "owner/repo/tools/ci-fixture.yml@refs/heads/dev", "ci-fixture.yml@refs/heads/dev"):
            with self.subTest(ref=ref):
                self.assert_error(self.resolve(workflow_ref=ref), "workflow ref")

    def test_registered_workflow_ref_resolves_on_any_ref(self):
        for ref in ("o/r/.github/workflows/ci-fixture.yml@refs/heads/dev",
                    "o/r/.github/workflows/ci-fixture.yml@refs/pull/9/merge"):
            with self.subTest(ref=ref):
                self.assertEqual(self.resolve(workflow_ref=ref).returncode, 0)

    def fingerprint(self, name="fixture-build"):
        (self.root / "Meta/engineering-projects.json").write_text(json.dumps(self.projects))
        (self.root / "Meta/ci-units.json").write_text(json.dumps(self.manifest))
        return subprocess.run([sys.executable, str(self.script), "fingerprint", name],
                              cwd=tempfile.gettempdir(), capture_output=True, text=True)

    def commit_tree(self, files):
        for path, text in files.items():
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        git = ["git", "-C", str(self.root), "-c", "user.name=t", "-c", "user.email=t@t"]
        if not (self.root / ".git").exists():
            subprocess.run(git + ["init", "-q"], check=True)
        subprocess.run(git + ["add", "-A"], check=True)

    def base_tree(self):
        return {"tests/T/A.cs": "a", "src/P/x/Nested/B.cs": "b", "shared/Exact.cs": "c",
                "config/build.props": "p", "unrelated/Other.cs": "u", "src/P/P.csproj": "p",
                "tests/T/T.csproj": "t", "src/D/D.csproj": "d"}

    def test_fingerprint_follows_compile_inputs_only(self):
        self.commit_tree(self.base_tree())
        first = self.fingerprint()
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertRegex(first.stdout, r"^[0-9a-f]{64}\n$")
        self.commit_tree({"unrelated/Other.cs": "changed"})
        self.assertEqual(self.fingerprint().stdout, first.stdout)
        for path in ("shared/Exact.cs", "src/P/x/Nested/B.cs", "config/build.props", "tests/T/T.csproj"):
            with self.subTest(path=path):
                self.commit_tree({path: "changed " + path})
                changed = self.fingerprint()
                self.assertEqual(changed.returncode, 0, changed.stderr)
                self.assertNotEqual(changed.stdout, first.stdout)
                first = changed

    def test_fingerprint_ignores_closure_excludes(self):
        self.manifest["closure_excludes"] = ["shared/"]
        self.commit_tree(self.base_tree())
        first = self.fingerprint()
        self.commit_tree({"shared/Exact.cs": "changed"})
        self.assertNotEqual(self.fingerprint().stdout, first.stdout)

    def test_fingerprint_rejects_unknown_or_malformed_caches(self):
        self.commit_tree(self.base_tree())
        result = self.fingerprint("missing")
        self.assertEqual(result.returncode, 2)
        self.assertIn("unknown cache", result.stderr)
        for caches in ({"fixture-build": {"project": "src/X/X.csproj", "inputs": []}},
                       {"fixture-build": {"project": "tests/T/T.csproj"}},
                       {"fixture-build": {"project": "tests/T/T.csproj", "inputs": [1]}}, []):
            with self.subTest(caches=caches):
                self.manifest["caches"] = caches
                result = self.fingerprint()
                self.assertEqual(result.returncode, 2, result.stdout)

    def test_diamond_references_are_deduplicated(self):
        self.projects["projects"][0]["references"].append("src/D/D.csproj")
        result = self.resolve()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.paths.read_text().splitlines().count("shared/Exact.cs"), 1)


if __name__ == "__main__":
    unittest.main()
