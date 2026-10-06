"""The downstream inventory consumer preserves authoritative report results."""
import json
import pathlib
import tempfile
import unittest
from pipeline import inventory


class PipelineTests(unittest.TestCase):
    def test_production_results_and_evidence_are_preserved(self):
        records = [{"key": {"theorem": "D5.A.t", "registration_module": "Reg.A"},
                    "state": state, "certificate": certificate, "diagnostic": diagnostic}
                   for state, certificate, diagnostic in [
                       ("declared_validated", {"evidence_ref": "checked"}, None),
                       ("declared_unresolved", None, "input.cannot_decode")]]
        records[1]["key"] = dict(records[1]["key"], theorem="D5.A.u")
        with tempfile.TemporaryDirectory() as folder:
            report = pathlib.Path(folder) / "report.json"
            report.write_text(json.dumps({"modules": [{"module": "Reg.A",
                "information_templates": {"records": records}}, {"module": "D5.A"}]}))
            actual = inventory(report, "D5")
            self.assertEqual(actual["records"], records)
            self.assertEqual(actual["modules"], 2)
            self.assertEqual(actual["registration_modules"], 1)
            self.assertEqual(actual["counts"], {"declared_validated": 1, "declared_unresolved": 1})
            self.assertEqual(inventory(report, "D5.B")["records"], [])
            report.write_text(json.dumps({"modules": [{"information_templates": {
                "records": [records[0], records[0]]}}]}))
            with self.assertRaisesRegex(ValueError, "duplicate"):
                inventory(report, "D5")
