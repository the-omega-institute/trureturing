"""The export reader preserves JSON semantics while releasing each module."""
import json
import pathlib
import tempfile
import unittest

class ReportStreamTests(unittest.TestCase):
    def test_streams_canonical_and_pretty_exports_across_utf8_boundaries(self):
        from report_stream import fields
        report = {"schema": "truth-é", "nodes": [{"name": "quoted \" name", "declarations": list(range(100))},
                  {"name": "two", "declarations": []}], "source_commit": "head", "exponent": 1e100}
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "report.json"
            for indent in (None, 2):
                path.write_text(json.dumps(report, ensure_ascii=False, indent=indent))
                actual, nodes = {}, []
                for key, value in fields(path, chunk_size=7):
                    if key == "nodes": nodes.append(value)
                    else: actual[key] = value
                actual["nodes"] = nodes
                self.assertEqual(actual, report)

    def test_rejects_truncated_duplicate_and_trailing_json(self):
        from report_stream import fields
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "report.json"
            for text in ('{"nodes": [{}', '{"nodes":[],"nodes":[]}', '{"nodes":[]} garbage',
                         '{"nodes":[{},]}', '{"nodes":[],}', '{"nodes": {}}'):
                path.write_text(text)
                with self.assertRaises(ValueError, msg=text): list(fields(path, chunk_size=3))

if __name__ == "__main__": unittest.main()
