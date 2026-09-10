"""The sidecar is an output-only consumer; census bytes remain authoritative."""

import hashlib
import json
import pathlib
import tempfile
import unittest
from unittest.mock import patch

from negative_fixtures import name_key


class StructureSidecarTests(unittest.TestCase):
    def test_publication_failure_is_a_receipt_not_a_census_rejection(self):
        from Structure.sidecar import run_sidecar
        with patch("Structure.sidecar.report_only", side_effect=OSError("publication unavailable")):
            receipt = run_sidecar(pathlib.Path("repository"), pathlib.Path("run"), pathlib.Path("report"))
        self.assertEqual(receipt["status"], "unavailable")
        self.assertEqual(receipt["publication_error"], "publication unavailable")

    def test_sidecar_failure_keeps_census_bytes_and_success(self):
        from Structure.sidecar import report_only
        with tempfile.TemporaryDirectory() as root:
            directory = pathlib.Path(root)
            census = b'{"counts":{"certified":1,"observed":1},"certified_complete":false}\n'
            (directory / "census.json").write_bytes(census)
            (directory / "request.json").write_text(json.dumps({
                "head": "fixture-head", "report_sha256": "fixture-report",
                "keys": [["Fixture", name_key("a"), "id-a"]]}))
            (directory / "olean-hashes.json").write_text("[]")

            def failed_reader():
                raise RuntimeError("injected extraction failure")

            receipt = report_only(directory, failed_reader)
            self.assertEqual((directory / "census.json").read_bytes(), census)
            self.assertEqual(receipt["status"], "unavailable")
            sidecar = json.loads((directory / "census-structure.json").read_bytes())
            self.assertEqual(sidecar["census_sha256"], "sha256:" + hashlib.sha256(census).hexdigest())
            self.assertEqual(sidecar["rows"][0]["status"], "unavailable")
            self.assertIsNone(sidecar["rows"][0]["readings"])

    def test_policy_is_the_panels_exact_core_set(self):
        from Structure.sidecar import core_policy
        policy, hashed = core_policy()
        self.assertEqual(len(policy), 52)
        self.assertEqual(hashed, "sha256:87ab7aef020a90dfef1fd1cbde8e49317f4ece4ddc9202445da83e82f5bb36c9")
        for excluded in ["Classical.choice", "propext", "sorryAx", "Lean.ofReduceBool", "Nat.rec"]:
            self.assertNotIn(excluded, policy)


if __name__ == "__main__":
    unittest.main()
