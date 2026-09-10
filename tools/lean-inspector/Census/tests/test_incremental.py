"""Content reuse and bounded validation are behavioral census contracts."""

import pathlib
import tempfile
import unittest


class IncrementalTests(unittest.TestCase):
    def test_stale_extraction_cache_reextracts_changed_olean_only(self):
        from incremental import extraction_plan, save_extraction
        with tempfile.TemporaryDirectory() as folder:
            cache = pathlib.Path(folder)
            modules = [["A", ["a"]], ["B", ["b"]]]
            hashes = [["A", "base", 10, "sha256:" + "a" * 64],
                      ["B", "base", 10, "sha256:" + "b" * 64]]
            first = extraction_plan(modules, hashes, cache, "source", "keys")
            self.assertEqual([m[0] for m in first["misses"]], ["A", "B"])
            for module in ("A", "B"):
                save_extraction(first, module, [{"module": module, "owners": []}])
            hashes[0][3] = "sha256:" + "c" * 64
            second = extraction_plan(modules, hashes, cache, "source", "keys")
            self.assertEqual([m[0] for m in second["misses"]], ["A"])
            self.assertEqual(second["hits"], ["B"])

    def test_extraction_cache_binds_frozen_name_universe_and_reader(self):
        from incremental import extraction_plan, save_extraction
        with tempfile.TemporaryDirectory() as folder:
            args = ([["A", ["a"]]], [["A", "base", 1, "sha256:" + "a" * 64]], pathlib.Path(folder))
            first = extraction_plan(*args, "reader", "keys")
            save_extraction(first, "A", [{"module": "A"}])
            self.assertEqual(extraction_plan(*args, "reader", "keys")["hits"], ["A"])
            self.assertEqual(extraction_plan(*args, "new-reader", "keys")["hits"], [])
            self.assertEqual(extraction_plan(*args, "reader", "new-keys")["hits"], [])

    def test_two_batches_respect_union_closure_bound(self):
        from incremental import candidate_batches
        graph = {"Init": [], "Command": ["Init"], "A": ["Init"], "B": ["Init"]}
        keys = [["A", "a", "id-a"], ["B", "b", "id-b"]]
        batches = candidate_batches(keys, {"A": ["A", "Command"], "B": ["B", "Command"]}, graph, 3)
        self.assertEqual(len(batches), 2)
        self.assertEqual([batch["keys"] for batch in batches], [[keys[0]], [keys[1]]])
        self.assertTrue(all(len(batch["modules"]) <= 3 for batch in batches))
        with self.assertRaisesRegex(ValueError, "IE-C044.*batch"):
            candidate_batches(keys, {"A": ["A", "Command"], "B": ["B", "Command"]}, graph, 2)

    def test_validation_cache_invalidates_only_changed_inputs(self):
        from incremental import validation_key
        args = (["A", "a", "id-a"], "owner-digest", [["Evidence", "digest"]], "lean", "query", "scope")
        baseline = validation_key(*args)
        for index in range(1, 6):
            changed = list(args)
            changed[index] = [["Evidence", "changed"]] if index == 2 else "changed"
            self.assertNotEqual(baseline, validation_key(*changed))
        self.assertEqual(baseline, validation_key(*args))

    def test_one_large_owner_is_split_by_key_bound(self):
        from incremental import candidate_batches
        keys = [["A", str(i), str(i)] for i in range(257)]
        batches = candidate_batches(keys, {"A": ["A"]}, {"A": []}, 1)
        self.assertEqual([len(batch["keys"]) for batch in batches], [128, 128, 1])
        self.assertEqual([key for batch in batches for key in batch["keys"]], keys)

    def test_upstream_header_memo_detects_same_size_rewrite(self):
        import json
        import os
        from unittest.mock import patch
        from phases import upstream_header
        with tempfile.TemporaryDirectory() as folder:
            root = pathlib.Path(folder)
            path, cache, memo = root / "A.ilean", root / "cache", {}
            path.write_text(json.dumps({"module": "A", "directImports": [["Old"]]}))
            old_stamp = path.stat()
            first, _, reread = upstream_header(path, memo, cache)
            self.assertEqual(first["imports"], ["Old"])
            self.assertTrue(reread)
            with patch.object(pathlib.Path, "read_bytes", side_effect=AssertionError("unchanged metadata was reread")):
                self.assertEqual(upstream_header(path, memo, cache), (first, True, False))
            path.write_text(json.dumps({"module": "A", "directImports": [["New"]]}))
            os.utime(path, ns=(old_stamp.st_atime_ns, old_stamp.st_mtime_ns))
            changed, _, reread = upstream_header(path, memo, cache)
            self.assertTrue(reread)
            self.assertEqual(changed["imports"], ["New"])

    def test_membership_cache_requires_exact_index_request_and_native_reader(self):
        from membership_cache import reuse
        with tempfile.TemporaryDirectory() as folder:
            root = pathlib.Path(folder)
            index, request = root / "index", root / "request"
            index.write_text("index-a")
            request.write_text("request-a")
            calls = []
            def compute(destination):
                calls.append(1)
                destination.write_text(index.read_text()+request.read_text())
                pathlib.Path(str(destination)+".rows.jsonl").write_text("rows")
            def run(reader="reader-a"):
                return reuse(index, request, reader, root / "cache", root / "output", compute)
            self.assertFalse(run()["hit"])
            self.assertTrue(run()["hit"])
            self.assertEqual(len(calls), 1)
            index.write_text("index-b")
            self.assertFalse(run()["hit"])
            request.write_text("request-b")
            self.assertFalse(run()["hit"])
            self.assertFalse(run("reader-b")["hit"])
            self.assertEqual(len(calls), 4)

    def test_expanded_rows_cache_binds_rows_scopes_and_emitter(self):
        from emission_cache import cache_key
        first = cache_key("rows-a", ["A"], [["Root", [0]]], "emitter-a")
        self.assertNotEqual(first, cache_key("rows-b", ["A"], [["Root", [0]]], "emitter-a"))
        self.assertNotEqual(first, cache_key("rows-a", ["B"], [["Root", [0]]], "emitter-a"))
        self.assertNotEqual(first, cache_key("rows-a", ["A"], [["Root", []]], "emitter-a"))
        self.assertNotEqual(first, cache_key("rows-a", ["A"], [["Root", [0]]], "emitter-b"))

    def test_expanded_rows_clone_rewrites_only_the_new_header(self):
        from emission_cache import store_rows, restore_rows
        with tempfile.TemporaryDirectory() as folder:
            root = pathlib.Path(folder)
            source = root / "source.json"
            source.write_bytes(b'{"head":"old","rows":[1,2,3]}')
            cache = root / "cache"
            old_header = b'{"head":"old","rows":'
            new_header = b'{"head":"new","rows":'
            stored = store_rows(cache, "sha256:"+"a"*64, source, len(old_header))
            if not stored: self.skipTest("filesystem clone unavailable; streaming fallback remains active")
            result = root / "result.json"
            self.assertTrue(restore_rows(cache, "sha256:"+"a"*64, result, new_header))
            self.assertEqual(result.read_bytes(), b'{"head":"new","rows":[1,2,3]}')
            self.assertEqual(source.read_bytes(), b'{"head":"old","rows":[1,2,3]}')
            self.assertFalse(restore_rows(cache, "sha256:"+"b"*64, root/"missing", new_header))
            self.assertFalse(restore_rows(cache, "sha256:"+"a"*64, root/"long", b"longer header"))


if __name__ == "__main__":
    unittest.main()
