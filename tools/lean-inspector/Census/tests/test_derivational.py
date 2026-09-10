"""Candidate publication is only a projection of the structural sidecar."""

import hashlib
import json
import pathlib
import tempfile
import unittest


def statement(name, identity):
    return {"theorem_name": ["str", ["anonymous"], name], "statement_id": identity}


def row(name, identity, support, *, generated=False, status="complete", leaves=()):
    return dict(statement(name, identity), owning_module="Fixture",
                generated_candidate=generated, status=status, readings={
                    "core_or_frozen_support": support,
                    "direct_frozen_prerequisites": list(leaves),
                    "value_constant_count": 3})


class DerivationalTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.directory = pathlib.Path(self.scratch.name)
        self.sidecar = self.directory / "census-structure.json"
        self.rows = [
            row("synthetic", "id-generated", True, generated=True),
            row("unknown", "id-unknown", "undetermined"),
            row("congr_simp", "id-hand", True, leaves=[statement("leaf", "id-leaf")]),
            row("partial", "id-partial", "undetermined", status="partial"),
            dict(statement("missing", "id-missing"), owning_module="Fixture",
                 status="unavailable", readings=None),
        ]
        self.write_rows()

    def write_rows(self):
        self.sidecar.write_text(json.dumps({"schema": "census-structure", "rows": self.rows}))

    def report(self):
        from Structure.derivational import build_report
        return build_report(self.sidecar)

    def test_only_support_positive_rows_and_exact_summary(self):
        report = self.report()
        self.assertEqual(report["candidates"], [
            {"key": statement("congr_simp", "id-hand"), "module": "Fixture",
             "theorem_name": statement("congr_simp", "id-hand")["theorem_name"],
             "generated_candidate": False, "direct_frozen_prerequisites": [statement("leaf", "id-leaf")],
             "value_constant_count": 3, "structural_status": "complete"},
            {"key": statement("synthetic", "id-generated"), "module": "Fixture",
             "theorem_name": statement("synthetic", "id-generated")["theorem_name"],
             "generated_candidate": True, "direct_frozen_prerequisites": [],
             "value_constant_count": 3, "structural_status": "complete"},
        ])
        self.assertEqual(report["summary"], {"candidates": 2, "generated": 1,
                         "non_generated": 1, "with_at_least_one_frozen_leaf": 1})

    def test_input_hash_binds_exact_bytes(self):
        expected = "sha256:" + hashlib.sha256(self.sidecar.read_bytes()).hexdigest()
        self.assertEqual(self.report()["input_sha256"], expected)
        before = self.report()
        with self.sidecar.open("a") as out:
            out.write("\n")
        after = self.report()
        self.assertNotEqual(before.pop("input_sha256"), after.pop("input_sha256"))
        self.assertEqual(before, after)

    def test_same_bytes_publish_identically_without_other_census_artifacts(self):
        from Structure.derivational import publish
        twin = self.directory / "twin"
        twin.mkdir()
        (twin / self.sidecar.name).write_bytes(self.sidecar.read_bytes())
        census = self.directory / "census.json"
        census.write_bytes(b"not JSON: must never be read or changed")
        before = {p.name: p.read_bytes() for p in self.directory.iterdir() if p.is_file()}
        first = publish(self.directory)
        second = publish(twin)
        self.assertEqual(first.read_bytes(), second.read_bytes())
        self.assertEqual(first.read_bytes(), publish(self.directory).read_bytes())
        for name, data in before.items():
            self.assertEqual((self.directory / name).read_bytes(), data)

    def test_partial_positive_preserves_structured_identity_and_status(self):
        self.rows = [row("same", "id-b", True, status="partial"), row("same", "id-a", True)]
        self.rows[0]["theorem_name"] = ["num", ["str", ["anonymous"], "é"], 7]
        self.write_rows()
        candidates = self.report()["candidates"]
        self.assertEqual(len(candidates), 2)
        partial = next(c for c in candidates if c["structural_status"] == "partial")
        self.assertEqual(partial["key"], {k: self.rows[0][k] for k in ("theorem_name", "statement_id")})

    def test_truthy_values_are_not_support_positive(self):
        self.rows = [row("excluded", str(i), support)
                     for i, support in enumerate([False, None, "true", 1, "undetermined"])]
        self.write_rows()
        self.assertEqual(self.report()["summary"], {"candidates": 0, "generated": 0,
                         "non_generated": 0, "with_at_least_one_frozen_leaf": 0})
        self.assertEqual(self.report()["candidates"], [])


if __name__ == "__main__":
    unittest.main()
