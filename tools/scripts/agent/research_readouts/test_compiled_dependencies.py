"""Contract for finite, explicitly scoped compiled dependency observations."""
import json
import io
from contextlib import redirect_stdout
from pathlib import Path
import subprocess
import sys
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
        result = subprocess.run([sys.executable, "-B", str(script), "--no-build"],
                                input=json.dumps(query), text=True, capture_output=True,
                                cwd=script.parent)
        self.assertEqual(result.returncode, 2, result.stderr)
        output = json.loads(result.stdout)
        self.assertFalse(output["complete"])
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


if __name__ == "__main__":
    unittest.main()
