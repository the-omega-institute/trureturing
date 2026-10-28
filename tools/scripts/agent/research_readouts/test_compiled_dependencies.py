"""Contract for finite, explicitly scoped compiled dependency observations."""
import json
import io
import os
from contextlib import redirect_stdout
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import compiled_dependencies as dependency


def declaration(name, module, types=None, value=None, kind="definition", private=False,
                internal=False):
    return dict(name=name, module=module, user_name=name, kind=kind,
                private=private, internal=internal, type=types or [], value=value)


def snapshot():
    return {"modules": [
        {"module": "A", "status": "ok", "imports": [], "declarations": [
            declaration("seed", "A", value=[]),
            declaration("Carrier", "A", kind="inductive"),
        ]},
        {"module": "B", "status": "ok", "imports": ["A"], "declarations": [
            declaration("typeOnly", "B", types=["seed"], value=[]),
            declaration("helper", "B", value=["seed"], private=True),
            declaration("use.match_1", "B", value=["helper"], internal=True),
            declaration("use", "B", value=["use.match_1"]),
            declaration("importOnly", "B", value=[]),
        ]},
    ]}


def request():
    return {"revision": "a" * 40, "domain": {"modules": ["A", "B"], "complete": True},
            "targets": ["seed"]}


class DependencyTests(unittest.TestCase):
    def read(self, raw=None, query=None, acquisition=None):
        return dependency.summarize(raw or snapshot(), query or request(),
                                    acquisition or {"status": "built", "complete": True})

    def test_types_imports_and_values_are_separate(self):
        result = self.read()
        rows = {r["name"]: r for r in result["declarations"]}
        self.assertEqual(rows["typeOnly"]["type"]["forward"]["direct"], ["seed"])
        self.assertEqual(rows["typeOnly"]["value"]["forward"]["direct"], [])
        self.assertEqual(result["queries"][0]["external_value_users"], ["use"])
        self.assertEqual(result["queries"][0]["external_value_user_count"], 1)
        modules = {m["module"]: m for m in result["modules"]}
        self.assertEqual(modules["A"]["imports"]["reverse"]["direct"], ["B"])
        self.assertNotIn("importOnly", rows["seed"]["value"]["reverse"]["transitive"])

    def test_private_and_generated_nodes_preserve_paths_without_extra_users(self):
        result = self.read()
        query = result["queries"][0]
        self.assertEqual(query["value_paths"]["use"],
                         ["use", "use.match_1", "helper", "seed"])
        self.assertEqual(query["external_value_user_count"], 1)
        self.assertEqual(len(result["declarations"]), 7)

    def test_absent_values_are_distinct_from_empty_expressions(self):
        rows = {r["name"]: r for r in self.read()["declarations"]}
        self.assertEqual(rows["Carrier"]["value"]["status"], "no_value")
        self.assertIsNone(rows["Carrier"]["value"]["forward"])
        self.assertEqual(rows["seed"]["value"]["forward"]["direct"], [])

    def test_missing_required_value_never_reports_exact_zero(self):
        raw = snapshot()
        raw["modules"][1]["declarations"][2]["value"] = None
        result = self.read(raw)
        self.assertFalse(result["complete"])
        self.assertIn("MISSING_REQUIRED_VALUE", {g["code"] for g in result["gaps"]})
        self.assertIsNone(result["queries"][0]["external_value_user_count"])

    def test_missing_module_unknown_target_and_incomplete_domain_are_named(self):
        for mode, code in [("module", "MISSING_MODULE"),
                           ("target", "UNKNOWN_DECLARATION"),
                           ("domain", "USER_DOMAIN_INCOMPLETE")]:
            raw, query = snapshot(), request()
            if mode == "module":
                raw["modules"].pop()
            elif mode == "target":
                query["targets"] = ["unknown"]
            else:
                query["domain"]["complete"] = False
            result = self.read(raw, query)
            self.assertFalse(result["complete"])
            self.assertIn(code, {g["code"] for g in result["gaps"]})
            self.assertIsNone(result["queries"][0]["external_value_user_count"])

    def test_failed_or_unverified_acquisition_cannot_become_exact_empty(self):
        for status in ("missing_artifacts", "build_failed", "freshness_unverified"):
            result = self.read(acquisition={"status": status, "complete": False})
            self.assertFalse(result["complete"])
            self.assertIsNone(result["queries"][0]["external_value_user_count"])

    def test_paths_do_not_silently_expand_the_declared_domain(self):
        raw = snapshot()
        raw["modules"][1]["declarations"][3]["value"] = ["outside"]
        result = self.read(raw)
        self.assertEqual(result["queries"][0]["external_value_user_count"], 0)
        self.assertEqual(result["path_scope"], "intermediate declarations in domain modules only")
        self.assertIn("outside", result["boundary_constants"])

    def test_cycles_terminate_and_do_not_count_the_root_as_its_own_user(self):
        raw = snapshot()
        raw["modules"][0]["declarations"][0]["value"] = ["use"]
        result = self.read(raw)
        root = next(r for r in result["declarations"] if r["name"] == "seed")
        self.assertNotIn("seed", root["value"]["forward"]["transitive"])
        self.assertEqual(result["queries"][0]["external_value_user_count"], 1)

    def test_request_requires_an_explicit_finite_domain_and_revision(self):
        for field in ("revision", "domain", "targets"):
            query = request()
            del query[field]
            with self.assertRaises(dependency.RequestError):
                dependency.validate_request(query)
        for value in ([], ["../x"], ["A", "A"], ["A;touch x"]):
            query = request()
            query["domain"]["modules"] = value
            with self.assertRaises(dependency.RequestError):
                dependency.validate_request(query)
        query = request()
        query["domain"]["complete"] = "yes"
        with self.assertRaises(dependency.RequestError):
            dependency.validate_request(query)

    def test_cli_missing_artifacts_is_json_from_another_working_directory(self):
        script = Path(dependency.__file__).resolve()
        query = request()
        root = script.parents[4]
        query["revision"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
        query["domain"]["modules"] = ["Missing.DependencyReadoutFixture"]
        # A protocol test must remain independent of installed Lean artifacts.
        # This sandbox inherits the enclosing Git revision but has no own cache.
        driver = ("import sys; from pathlib import Path; "
                  "sys.path.insert(0, sys.argv[1]); import compiled_dependencies as d; "
                  "d.ROOT=Path(sys.argv[2]); sys.argv=['compiled_dependencies.py','--no-build']; "
                  "raise SystemExit(d.main())")
        with tempfile.TemporaryDirectory(prefix="dependency protocol ", dir=script.parent) as sandbox:
            result = subprocess.run([sys.executable, "-B", "-c", driver,
                                     str(script.parent), sandbox],
                                    input=json.dumps(query), text=True, capture_output=True,
                                    cwd=sandbox)
        self.assertEqual(result.returncode, 2, result.stderr)
        output = json.loads(result.stdout)
        self.assertFalse(output["complete"])
        self.assertEqual(output["acquisition"]["status"], "missing_artifacts")
        self.assertIsNone(output["queries"][0]["external_value_user_count"])

    def test_runtime_failure_keeps_named_incomplete_queries(self):
        output = io.StringIO()
        with patch.object(sys, "stdin", io.StringIO(json.dumps(request()))), \
                patch.object(sys, "argv", ["compiled_dependencies.py"]), \
                patch.object(dependency, "acquire", side_effect=OSError("lake unavailable")), \
                redirect_stdout(output):
            self.assertEqual(dependency.main(), 2)
        result = json.loads(output.getvalue())
        self.assertFalse(result["complete"])
        self.assertIsNone(result["queries"][0]["external_value_user_count"])


class DependencyEntryTests(unittest.TestCase):
    """Real make/acquire/Main execution using the existing core-only native fixture."""

    @classmethod
    def setUpClass(cls):
        sys.path.insert(0, str(dependency.ROOT / "tools/lean-inspector/tests"))
        from test_native_support import NativeTestSupport

        class Fixture(NativeTestSupport, unittest.TestCase):
            pass

        Fixture.setUpClass()
        cls.fixture_type = Fixture

    def setUp(self):
        temporary_root = dependency.ROOT / ".lake"
        temporary_root.mkdir(exist_ok=True)
        parent = tempfile.TemporaryDirectory(prefix="dependency entry ", dir=temporary_root)
        self.addCleanup(parent.cleanup)
        self.fixture = fixture = self.fixture_type()
        with patch.dict(os.environ, {"STRATALINT_NATIVE_TMPDIR": parent.name}):
            fixture.setUp()
        self.addCleanup(fixture.cleanup_fixture)
        for name in ["tools/Makefile",
                     "tools/scripts/agent/research_readouts/compiled_dependencies.py",
                     "tools/lean-inspector/DependencyReadoutMain.lean",
                     "tools/lean-inspector/LeanInformationAudit/DependencyReadout.lean",
                     "tools/lean-inspector/LeanInformationAudit/Registry/Repository.lean",
                     "tools/lean-inspector/LeanInformationAuditRegTests/DependencyFixtures/Base.lean",
                     "tools/lean-inspector/LeanInformationAuditRegTests/DependencyFixtures/Users.lean"]:
            fixture.copy(name)
        config = fixture.root / "tools/lean-inspector/lakefile.lean"
        source = config.read_text()
        source = source.replace("roots := #[`LeanInformationAudit.RawArtifacts",
            "roots := #[`LeanInformationAudit.DependencyReadout, `LeanInformationAudit.Registry.Repository, "
            "`LeanInformationAudit.RawArtifacts")
        source = source.replace("globs := #[.one `LeanInformationAudit.RawArtifacts",
            "globs := #[.one `LeanInformationAudit.DependencyReadout, .one `LeanInformationAudit.Registry.Repository, "
            ".one `LeanInformationAudit.RawArtifacts")
        config.write_text(source)
        # Route the unmodified cache entry to the same built producer used by native tests.
        # Cold-build consent applies only to this private core-only project.
        fixture.env.update(STRATALINT_LEAN_PRODUCER_DLL=str(fixture.cli),
                           STRATALINT_ACCEPT_COLD_BUILD="1",
                           PATH=os.pathsep.join([str(Path(fixture.dotnet).parent),
                                               str(Path(fixture.lake).parent), os.environ["PATH"]]))
        fixture.write(".gitignore", ".lake/\n")
        subprocess.run(["git", "-C", str(fixture.root), "add", "."], check=True, capture_output=True)
        subprocess.run(["git", "-C", str(fixture.root), "-c", "user.name=Fixture",
                        "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgsign=false",
                        "commit", "-qm", "compiled dependency fixture"], check=True, capture_output=True)
        self.revision = subprocess.check_output(
            ["git", "-C", str(fixture.root), "rev-parse", "HEAD"], text=True).strip()
        receipt = fixture.ensure()
        self.assertEqual(receipt["project_olean_state"], "cold")

    def read(self, targets, expected_exit):
        fixture = self.fixture
        program = fixture.root / ".lake/build/lean-inspector/producer/bin/dependencyReadout"
        self.assertFalse(program.exists(), "the production make entry must build the executable")
        query = {"revision": self.revision,
                 "domain": {"modules": ["LeanInformationAuditRegTests.DependencyFixtures.Base",
                                        "LeanInformationAuditRegTests.DependencyFixtures.Users"],
                            "complete": True}, "targets": targets}
        fixture.write("request.json", json.dumps(query))
        result = fixture.guarded_command(["/bin/bash", "-c",
            'exec make -s --no-print-directory -C "$1" compiled-dependencies DEPENDENCY_NO_BUILD=0 < "$2"',
            "dependency-entry", str(fixture.root / "tools"), str(fixture.root / "request.json")],
            cwd=fixture.root / "tools", env=fixture.env)
        diagnostic = "[FAIL] CompiledDependencyProductionEntry: " + result.stdout + result.stderr
        self.assertEqual(result.returncode, expected_exit, diagnostic)
        output = json.loads(result.stdout)
        self.assertEqual(output["schema"], "compiled-dependencies-v1")
        self.assertEqual(output["revision"], self.revision)
        self.assertEqual(output["acquisition"]["status"], "built", diagnostic)
        self.assertTrue(output["acquisition"]["complete"], diagnostic)
        self.assertEqual(output["acquisition"]["build_exit"], 0)
        self.assertEqual(output["acquisition"]["reader_exit"], 0)
        self.assertTrue(program.is_file())
        return output

    def test_production_entry_reads_value_users_separately_from_types_and_imports(self):
        output = self.read(["DependencyFixture.seed", "DependencyFixture.Token"], 0)
        self.assertTrue(output["complete"])
        self.assertEqual(output["gaps"], [])
        seed, token = output["queries"]
        self.assertIn("DependencyFixture.Users.direct", seed["external_value_users"])
        self.assertIn("DependencyFixture.Users.throughHelper", seed["external_value_users"])
        self.assertNotIn("DependencyFixture.Users.typeOnly", seed["external_value_users"])
        self.assertNotIn("DependencyFixture.Users.importOnly", seed["external_value_users"])
        self.assertEqual(seed["external_value_user_count"], len(seed["external_value_users"]))
        self.assertEqual(seed["value_paths"]["DependencyFixture.Users.direct"],
                         ["DependencyFixture.Users.direct", "DependencyFixture.seed"])
        self.assertEqual(token["external_value_users"], [])
        self.assertEqual(token["external_value_user_count"], 0)
        rows = {row["name"]: row for row in output["declarations"]}
        self.assertIn("DependencyFixture.Token",
                      rows["DependencyFixture.Users.typeOnly"]["type"]["forward"]["direct"])
        self.assertNotIn("DependencyFixture.Token",
                         rows["DependencyFixture.Users.typeOnly"]["value"]["forward"]["transitive"])
        modules = {row["module"]: row for row in output["modules"]}
        self.assertTrue(all(row["status"] == "ok" for row in modules.values()))
        self.assertIn("LeanInformationAuditRegTests.DependencyFixtures.Base",
                      modules["LeanInformationAuditRegTests.DependencyFixtures.Users"]["imports"]["forward"]["direct"])

    def test_production_entry_names_unknown_declaration_without_an_exact_count(self):
        missing = "DependencyFixture.missingDeclaration"
        output = self.read([missing], 2)
        self.assertFalse(output["complete"])
        self.assertEqual(output["gaps"], [{"code": "UNKNOWN_DECLARATION", "subject": missing}])
        query, = output["queries"]
        self.assertEqual(query["status"], "incomplete")
        self.assertIsNone(query["external_value_user_count"])


if __name__ == "__main__":
    unittest.main(defaultTest="DependencyTests")
