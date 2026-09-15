"""Binding transport controls; native join behavior has separate Lean fixtures."""

import copy
import hashlib
import json
import pathlib
import tempfile
import unittest
from unittest.mock import patch

from bindings import absent, incomplete, validate
from incremental import atomic_json
from streaming import canonical
from validation import prepare, run_batches


class TemplateBindingTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repo = pathlib.Path(self.temporary.name)
        self.directory = self.repo / "run"
        self.directory.mkdir()
        self.cache = self.repo / "cache"
        (self.repo / "lean-toolchain").write_text("fixture-toolchain")
        (self.repo / "lake-manifest.json").write_text("{}")
        (self.repo / "Owner.lean").write_text("fixture owner")
        (self.repo / "Sidecar.lean").write_text("fixture sidecar")
        graph = {"Owner": [], "Sidecar": ["Owner"], "LeanInformationAudit.Census.Command": []}
        names = sorted(graph)
        self.key = ["Owner", "ns(n0,6:target)", "identity"]
        self.membership = {"candidate_keys": [self.key], "module_names": names,
            "external_graph": sorted(graph.items()), "headers": [], "named": [],
            "evidence_modules": ["Sidecar"], "errors": [], "assignment": {"Owner": "Root"},
            "scopes": [["Root", list(range(len(names)))]]}
        atomic_json(self.directory / "olean-hashes.json", [
            [name, "base", 1, "sha256:" + "a" * 64] for name in ["Owner", "Sidecar"]])
        atomic_json(self.directory / "domain.json", {name: name + ".lean" for name in ["Owner", "Sidecar"]})
        atomic_json(self.directory / "report.json", {"nodes": [
            {"repo_path": "Owner.lean", "declarations": [{"statement_id": self.key[2]}]}]})
        self.request = {"head": "fixture-head", "keys": [self.key],
                        "report": str(self.directory / "report.json")}
        # This fixture has no Git producer sources; all native values below are
        # explicit synthetic output, never a claim of Lean certification.
        mock = patch("validation.subprocess.check_output", return_value=b"")
        mock.start()
        self.addCleanup(mock.stop)

    def plan(self):
        return prepare(self.repo, self.directory, self.membership, self.request, cache=self.cache)

    def evidence(self):
        key = {"root": "Owner", "registration_module": "Owner", "theorem": "target",
               "object_arena": "arena", "catalog": "catalog"}
        return dict(absent(), records=[{"key": key, "state": "declared_validated", "diagnostic": None,
                    "certificate": {"key": key, "evidence_ref": "b" * 64}}], source_inputs=[
                    {"path": "Sidecar.lean", "sha256": hashlib.sha256((self.repo / "Sidecar.lean").read_bytes()).hexdigest()}])

    def run_plan(self, plan):
        def step(command, label, **kwargs):
            folder = pathlib.Path(command[-1]).parent
            batch_request = json.loads((folder / "request.json").read_bytes())
            self.assertIn("Sidecar", json.loads((folder / "index.json").read_bytes())["evidence_modules"])
            value = {"entries": [{"statement_id": self.key[2], "class": "observed"}],
                "source_inputs": [], "key_source_inputs": [[self.key[2], []]],
                "key_binding_evidence": [[self.key[2], self.evidence()]], "environment_modules": 3}
            atomic_json(folder / "candidates.json", value)
            atomic_json(folder / "candidates.json.receipt.json", {"head": "fixture-head",
                "report_sha256": batch_request["report_sha256"],
                "rows_sha256": "sha256:" + hashlib.sha256(canonical(value)).hexdigest()})
            return {"peak_rss_bytes": 4096}
        return run_batches(self.repo, self.directory, self.membership, self.request, plan, step, "fixture-lean")[0]

    def test_census_binding_cache_roundtrip(self):
        cold = self.run_plan(self.plan())
        warm = self.plan()
        self.assertEqual(warm["execute"], [])
        self.assertEqual(self.run_plan(warm), cold, "[FAIL] census_binding_cache_roundtrip")

    def test_census_binding_cache_fresh_result(self):
        result = self.run_plan(self.plan())
        self.assertEqual(result["binding_evidence"], [[self.key, self.evidence()]])
        self.assertEqual(result["entries"][0]["class"], "observed")

    def test_census_binding_cache_missing_fields_rejected(self):
        self.run_plan(self.plan())
        cache = next(self.cache.glob("*.json"))
        value = json.loads(cache.read_bytes())
        del value["binding_evidence"]
        atomic_json(cache, value)
        with self.assertRaisesRegex(ValueError, "dtr.census_cache"):
            self.plan()

    def test_census_changed_sidecar_invalidates_binding(self):
        self.run_plan(self.plan())
        # An unchanged artifact/input-key cannot bless a stale recorded source.
        from bindings import sources_current
        evidence = self.evidence()
        (self.repo / "Sidecar.lean").write_text("changed sidecar")
        self.assertFalse(sources_current(self.repo, evidence))
        self.assertEqual(self.plan()["misses"], [self.key])

    def test_uncertified_states_cannot_transport_certificate(self):
        for state in ("undeclared", "declared_unresolved"):
            value = copy.deepcopy(self.evidence())
            value["records"][0]["state"] = state
            with self.assertRaises(ValueError):
                validate(value)
        self.assertFalse(validate(incomplete("missing sidecar"))["query_completed"])

    def test_census_undeclared_diagnostic_required(self):
        value = self.evidence()
        row = value["records"][0]
        row.update(state="undeclared", certificate=None, diagnostic=None)
        with self.assertRaises(ValueError, msg="[FAIL] census_undeclared_diagnostic_required"):
            validate(value)
        row["diagnostic"] = ('IE-C050 ClosedTruthReadout key=Owner/catalog/target '
            'reason=unclassified_form rule=dtr.missing_declaration site="" readout="" '
            'provenance={"argument_inputs":[],"extraction_inputs":[],"plan_identity":null,'
            '"rule":"dtr.missing_declaration","site":"","template_key":null}')
        self.assertIs(validate(value), value)
        row["diagnostic"] = row["diagnostic"].replace("Owner/catalog/target", "Other/catalog/target")
        with self.assertRaises(ValueError, msg="[FAIL] census_undeclared_diagnostic_required"):
            validate(value)


if __name__ == "__main__":
    unittest.main()
