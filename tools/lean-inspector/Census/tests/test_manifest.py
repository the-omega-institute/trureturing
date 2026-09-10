"""Independent authorities for emitted kernel keys and report keys."""

import unittest

from Certificate import emission


class ManifestTests(unittest.TestCase):
    def test_strict_statement_identity_codec(self):
        for value in (0, 1, 2 ** 256 - 1):
            wire = "sha256:" + format(value, "064x")
            self.assertEqual(emission.statement_nat(wire), value)
        for wire in ("0" * 64, "sha256:" + "0" * 63, "sha256:" + "0" * 65,
                     "sha256:" + "A" * 64, " sha256:" + "0" * 64,
                     "sha256:" + "0" * 64 + " ", "sha256:+" + "0" * 63):
            with self.subTest(wire=wire), self.assertRaisesRegex(ValueError, "statement_id_format"):
                emission.statement_nat(wire)

    def test_structured_name_decoder_preserves_constructor_identity(self):
        self.assertEqual(emission.parse_name_key("ns(n0,3:a.b)"), ["str", ["anonymous"], "a.b"])
        self.assertEqual(emission.parse_name_key("nn(ns(n0,1:A),3)"),
                         ["num", ["str", ["anonymous"], "A"], 3])
        self.assertNotEqual(emission.parse_name_key("nn(ns(n0,1:A),3)"),
                            emission.parse_name_key("ns(ns(n0,1:A),1:3)"))
        self.assertEqual(emission.parse_name_key("ns(n0,2:\u00e9)"), ["str", ["anonymous"], "\u00e9"])

    def test_report_keys_are_rendered_from_the_report(self):
        wire = "sha256:" + "0" * 64
        rows = [{"theorem_name": ["str", ["anonymous"], "Inventory"], "statement_id": wire}]
        report_keys = [("Fixture", "ns(n0,6:Report)", "sha256:" + format(1, "064x"))]
        source = emission.bucket_sources(rows, report_keys)["CensusRun.Range8_0"]
        before, after = source.split("def CensusRun.Range8_0.reportKeys.chunk", 1)
        self.assertIn("CensusRun.Range8_0.manifestKeys.chunk0 : Nat := 0x0", before)
        self.assertIn("0 : Nat := 0x1", after)
        self.assertNotIn('"Inventory"', source)
        self.assertNotIn('"Report"', source)
        self.assertNotIn(wire, source)

    def test_manifest_literals_are_canonical_and_deterministic(self):
        keys = [("Fixture", f"ns(n0,1:{name})", "sha256:" + format(n, "064x"))
                for name, n in (("B", 2), ("A", 1))]
        rows = [{"theorem_name": emission.parse_name_key(key), "statement_id": wire}
                for _, key, wire in keys]
        first = emission.manifest_source(rows, keys, "head", "digest", "Root")
        self.assertEqual(first, emission.manifest_source(rows[::-1], keys[::-1], "head", "digest", "Root"))
        self.assertNotIn("CensusRun.Rows", first)
        self.assertNotIn("DispositionCensus", first)

    def test_noncomputable_independent_chunks_are_bounded(self):
        keys = [("Fixture", "ns(n0,1:T)", "sha256:" + format(n, "064x")) for n in range(125)]
        rows = [{"theorem_name": emission.parse_name_key(key), "statement_id": wire}
                for _, key, wire in keys]
        source = emission.bucket_sources(rows, keys)["CensusRun.Range8_0"]
        self.assertEqual(source.count("noncomputable def"), 6)
        self.assertEqual(source.count("List.flatten"), 2)
        self.assertIn("import LeanInformationAudit.Census.Certificate\n", source)
        self.assertNotIn("Census.Publish", source)
        for side in ("manifestKeys", "reportKeys"):
            for number, expected in enumerate((100, 25)):
                body = source.split(f"def CensusRun.Range8_0.{side}.chunk{number} :", 1)[1].split(
                    "noncomputable def", 1)[0]
                packed = int(body.split(":=", 1)[1].split()[0], 0)
                decoded = []
                for _ in range(expected):
                    packed, digit = divmod(packed, 2 ** 256)
                    decoded.append(digit)
                self.assertEqual(packed, 0)
                self.assertEqual(decoded, list(range(number * 100, number * 100 + expected)))
                self.assertIn(f"decodeIds {expected} CensusRun.Range8_0.{side}.chunk{number}", source)
        self.assertNotIn("Lean.Name × Nat", source)
        self.assertNotIn("List.Nodup", source)

    def test_packing_rejects_out_of_domain_digits(self):
        for values in ([2 ** 256], [-1], [0] * 101, []):
            with self.subTest(values=values), self.assertRaises(ValueError):
                emission.pack_ids(values)

    def test_zero_high_digit_has_explicit_arity(self):
        self.assertEqual(emission.pack_ids([1, 0]), 1)
        source = emission.chunked_keys("Ids", [(["anonymous"], "sha256:" + "0" * 64)])
        self.assertIn("decodeIds 1 Ids.chunk0", source)
        self.assertIn("Ids.chunk0 : Nat := 0x0", source)


if __name__ == "__main__":
    unittest.main()
