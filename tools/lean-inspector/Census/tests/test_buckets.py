"""Executable contract for independent prefix partitions and incremental identity."""

import unittest

import pathlib
import sys

if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from Certificate import emission


def authorities(values):
    rows = [{"theorem_name": ["str", ["anonymous"], f"T{n}"],
             "statement_id": "sha256:" + format(n, "064x")} for n in values]
    keys = [("Fixture", f"ns(n0,{len(f'T{n}')}:{f'T{n}'})", row["statement_id"])
            for n, row in zip(values, rows)]
    return rows, keys


class BucketTests(unittest.TestCase):
    def test_every_prefix_including_empty_is_emitted(self):
        rows, keys = authorities([0, 1, 2 ** 255, 2 ** 256 - 1])
        buckets = emission.bucket_sources(rows, keys, b=8)
        self.assertEqual(sum("public import LeanInformationAudit.Census.Certificate" in s for s in buckets.values()), 256)
        self.assertIn("CensusRun.Range8_255", buckets)
        self.assertIn("n : Nat := 0", buckets["CensusRun.Range8_1"])
        self.assertIn("inRange 255 8", buckets["CensusRun.Range8_255"])

    def test_one_added_key_changes_exactly_one_module(self):
        rows, keys = authorities([0, 2 ** 255])
        before = emission.bucket_sources(rows, keys, b=8)
        rows, keys = authorities([0, 7 * 2 ** 248, 2 ** 255])
        after = emission.bucket_sources(rows, keys, b=8)
        self.assertEqual([name for name in before if before[name] != after[name] and "public import LeanInformationAudit.Census.Certificate" in before[name]],
                         ["CensusRun.Range8_7"])

    def test_assembly_has_no_packed_ids_and_uses_bucket_lemmas(self):
        rows, keys = authorities([2 ** 255 + 1])
        source = emission.manifest_source(rows, keys, "head", "digest", "CensusRun.Root", b=2)
        self.assertNotIn("0x", source)
        self.assertNotIn("decodeIds", source)
        self.assertEqual(source.count("range_join"), 1)
        self.assertIn("CensusRun.Range1_1.facts", source)

    def test_prefix_knob_and_order_do_not_change_proofs(self):
        rows, keys = authorities([0, 2 ** 256 - 1])
        for bits in [0, 1, 4, 8]:
            first = emission.bucket_sources(rows, keys, b=bits)
            self.assertEqual(first, emission.bucket_sources(rows[::-1], keys[::-1], b=bits))
            self.assertEqual(sum("public import LeanInformationAudit.Census.Certificate" in s for s in first.values()), 2 ** bits if bits else 0)
        for bits in [-1, 257]:
            with self.assertRaises(ValueError):
                emission.bucket_sources(rows, keys, b=bits)


if __name__ == "__main__":
    unittest.main()
