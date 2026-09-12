"""Candidate publication is only a projection of the structural sidecar."""

import hashlib
import io
import json
import pathlib
import subprocess
import sys
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
        from Structure.derivational import publish
        return json.loads(publish(self.directory).read_bytes())

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

    def test_streamed_hashes_match_published_bytes(self):
        from Structure.derivational import publish
        receipt = {}
        output = publish(self.directory, receipt=receipt)
        self.assertEqual(receipt["input_sha256"], "sha256:" + hashlib.sha256(self.sidecar.read_bytes()).hexdigest())
        self.assertEqual(receipt["output_sha256"], "sha256:" + hashlib.sha256(output.read_bytes()).hexdigest())
        self.assertEqual(receipt["summary"], json.loads(output.read_bytes())["summary"])

    def test_projected_reader_preserves_json_across_chunk_boundaries(self):
        from Structure.derivational_stream import Reader, rows
        leaf = statement('é " \\ \n', "id-leaf")
        self.rows = [row('é " \\ \n', "id-a", True, leaves=[leaf]), row("empty", "id-b", False)]
        self.rows[0]["unused"] = {"frontier": ["\\\"" * 100, -1.5e-100, None, True]}
        self.rows[0]["readings"]["unused"] = [{"array": [False]}] * 10
        for indent in (None, 2):
            encoded = json.dumps({"unused": [0, 1, {}], "rows": self.rows}, indent=indent,
                                 ensure_ascii=False).encode()
            for size in (1, 7, 65536):
                reader = Reader(io.BytesIO(encoded), chunk_size=size)
                with tempfile.TemporaryFile() as leaves:
                    actual = []
                    for item in rows(reader, leaves):
                        leaves.seek(0)
                        actual.append((item, json.loads(leaves.read())))
                self.assertEqual(actual[0][0]["theorem_name"], self.rows[0]["theorem_name"])
                self.assertEqual(actual[0][1], [leaf])
                self.assertEqual(actual[1][1], [])
                self.assertNotIn("unused", actual[0][0])
                self.assertNotIn("unused", actual[0][0]["readings"])
                self.assertEqual(reader.sha256.hexdigest(), hashlib.sha256(encoded).hexdigest())

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

    def test_identical_structured_names_keep_distinct_statement_ids(self):
        self.rows = [row("same", "id-b", True), row("same", "id-a", True)]
        self.write_rows()
        report = self.report()
        self.assertEqual([c["key"] for c in report["candidates"]],
                         [statement("same", "id-a"), statement("same", "id-b")])
        self.assertEqual(report["summary"]["candidates"], 2)

    def test_candidate_and_frontier_scaling_has_bounded_peak_rss(self):
        results = [json.loads(subprocess.check_output([
            sys.executable, "-B", "-m", "tests.derivational_memory_probe", str(rows), str(mib), mode],
            cwd=pathlib.Path(__file__).resolve().parents[1], text=True))
            for rows, mib, mode in [(1000, 0, "ignored"), (100000, 0, "ignored"),
                                   (1, 1, "ignored"), (1, 32, "ignored"),
                                   (1, 1, "selected"), (1, 32, "selected")]]
        print("DERIVATIONAL_RSS " + json.dumps(results), flush=True)
        for small, large in zip(results[::2], results[1::2]):
            self.assertLess(large["rss_bytes"] - small["rss_bytes"], 16 * 1024 ** 2,
                            "boundedDerivationalRSS")
        for result in results:
            expected = 0 if result["frontier_mib"] and result["mode"] == "ignored" else result["rows"]
            self.assertEqual(result["candidates"], expected)

    def test_invalid_input_preserves_previous_publication_and_cleans_scratch(self):
        from Structure.derivational import publish
        output = publish(self.directory)
        before = output.read_bytes()
        names = {p.name for p in self.directory.iterdir()}
        for text in ('{"rows":[{},]}', '{"rows":[],"rows":[]}',
                     '{"rows":[],"ignored":["unterminated]}',
                     '{"rows":[],"ignored":[1,]}', '{"rows":[]} trailing',
                     '{"rows":[],"ignored":01}', '{"rows":[],"ignored":1e}',
                     '{"rows":[],"ignored":"\\x"}', '{"rows":[],"ignored":"\\u123"}',
                     '{"rows":[],"ignored":{"a":true,}}'):
            self.sidecar.write_text(text)
            with self.subTest(text=text), self.assertRaises(ValueError):
                publish(self.directory)
            self.assertEqual(output.read_bytes(), before)
            self.assertEqual({p.name for p in self.directory.iterdir()}, names)

    def test_truthy_values_are_not_support_positive(self):
        self.rows = [row("excluded", str(i), support)
                     for i, support in enumerate([False, None, "true", 1, "undetermined"])]
        self.write_rows()
        self.assertEqual(self.report()["summary"], {"candidates": 0, "generated": 0,
                         "non_generated": 0, "with_at_least_one_frozen_leaf": 0})
        self.assertEqual(self.report()["candidates"], [])


if __name__ == "__main__":
    unittest.main()
