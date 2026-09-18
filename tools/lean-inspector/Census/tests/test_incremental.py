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
        batches, skipped = candidate_batches(keys, {"A": ["A", "Command"], "B": ["B", "Command"]}, graph, 3)
        self.assertEqual(skipped, [])
        self.assertEqual(len(batches), 2)
        self.assertEqual([batch["keys"] for batch in batches], [[keys[0]], [keys[1]]])
        self.assertTrue(all(len(batch["modules"]) <= 3 for batch in batches))
        batches, skipped = candidate_batches(keys, {"A": ["A", "Command"], "B": ["B", "Command"]}, graph, 2)
        self.assertEqual(batches, [])
        self.assertEqual([entry["owner"] for entry in skipped], ["A", "B"])

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
        batches, skipped = candidate_batches(keys, {"A": ["A"]}, {"A": []}, 1)
        self.assertEqual(skipped, [])
        self.assertEqual([len(batch["keys"]) for batch in batches], [128, 128, 1])
        self.assertEqual([key for batch in batches for key in batch["keys"]], keys)

    @staticmethod
    def mixed_owner_fixture():
        from validation import COMMAND
        graph = {"Init": [], COMMAND: ["Init"], "A": ["Extra"],
                 "Extra": ["More"], "More": ["Init"], "B": ["Init"]}
        keys = [["A", "ns(n0,1:a)", "sha256:" + "0" * 64]] + [
            ["B", f"nn(n0,{i})", "sha256:" + format(i + 1, "064x")] for i in range(129)]
        return graph, keys, {owner: [owner, COMMAND] for owner in ("A", "B")}

    def test_over_bound_owner_is_recorded_while_other_owner_splits(self):
        from incremental import candidate_batches
        graph, keys, imports = self.mixed_owner_fixture()
        batches, skipped = candidate_batches(keys, imports, graph, 4)
        self.assertEqual([len(batch["keys"]) for batch in batches], [128, 1])
        self.assertEqual([key for batch in batches for key in batch["keys"]], keys[1:])
        self.assertTrue(all(len(batch["modules"]) == 3 for batch in batches))
        self.assertEqual(skipped, [{"owner": "A", "modules": 5, "bound": 4, "keys": keys[:1],
            "diagnostic": "IE-C044 candidate batch owner=A modules=5 bound=4"}])
        self.assertNotIn("A", {module for batch in batches for module in batch["modules"]})
        del graph["More"]
        with self.assertRaisesRegex(ValueError, "IE-C044 missing import header: More"):
            candidate_batches(keys, imports, graph, 4)

    def test_skipped_owner_receipt_and_accounting_survive_cache_warmth(self):
        import hashlib
        import json
        from emission import parse_name_key
        from incremental import atomic_json
        from phases import name_json
        from streaming import canonical, closure
        from validation import prepare, run_batches
        graph, keys, imports = self.mixed_owner_fixture()
        names = sorted(graph)
        membership = {"candidate_keys": keys, "module_names": names,
            "external_graph": sorted(graph.items()), "headers": [], "named": [], "evidence_modules": [], "errors": [],
            "assignment": {owner: owner for owner in imports},
            "scopes": [[owner, [names.index(m) for m in closure(graph, required)]]
                       for owner, required in imports.items()]}
        repository = pathlib.Path(__file__).resolve().parents[4]
        with tempfile.TemporaryDirectory() as temporary:
            directory = pathlib.Path(temporary)
            cache = directory / "cache"
            atomic_json(directory / "olean-hashes.json", [
                [owner, "base", 1, "sha256:" + owner.lower() * 64] for owner in imports])
            atomic_json(directory / "domain.json", {owner: owner + ".lean" for owner in imports})
            atomic_json(directory / "report.json", {"source_commit": "fixture-head", "nodes": [
                {"repo_path": owner + ".lean", "declarations": [
                    {"statement_id": k[2]} for k in keys if k[0] == owner]} for owner in imports]})
            request = {"head": "fixture-head", "keys": keys, "report": str(directory / "report.json")}
            # A former assessment under a looser bound cannot bypass planning.
            wider = prepare(repository, directory, membership, request, bound=5, cache=cache)
            cache.mkdir()
            (cache / (wider["addresses"][keys[0][2]][7:] + ".json")).write_text("unreadable old assessment")
            plan = prepare(repository, directory, membership, request, bound=4, cache=cache)
            self.assertEqual(plan["misses"], keys[1:])
            self.assertNotIn(keys[0][2], plan["addresses"])
            calls = []

            def step(command, label, **kwargs):
                folder = pathlib.Path(command[-1]).parent
                batch_request = json.loads((folder / "request.json").read_bytes())
                batch = plan["execute"][len(calls)]
                calls.append(label)
                rows = [{"theorem_name": parse_name_key(name), "statement_id": identity,
                    "class": "observed", "payload": {"owning_module": name_json(owner),
                        "root": name_json(owner), "import_scope": None, "query_completed": True,
                        "candidates": [], "note": "fixture assessment"}}
                    for owner, name, identity in batch_request["keys"]]
                value = {"entries": rows, "source_inputs": [],
                    "key_binding_evidence": [[k[2], __import__("bindings").absent()] for k in batch_request["keys"]],
                    "key_source_inputs": [[k[2], []] for k in batch_request["keys"]],
                    "environment_modules": len(batch["modules"])}
                atomic_json(folder / "candidates.json", value)
                atomic_json(folder / "candidates.json.receipt.json", {
                    "head": request["head"], "report_sha256": batch_request["report_sha256"],
                    "environment_modules": value["environment_modules"],
                    "rows_sha256": "sha256:" + hashlib.sha256(canonical(value)).hexdigest()})
                return {"peak_rss_bytes": 4096}

            result, record = run_batches(repository, directory, membership, request, plan, step, "fixture-lean")
            self.assertEqual(len(calls), 2)
            self.assertEqual(len(result["entries"]), len(keys))
            self.assertEqual([e["peak_rss_bytes"] for e in record["executions"]], [4096, 4096])
            skipped = record["receipt"]["skipped"]
            self.assertEqual([(s["owner"], s["modules"], s["bound"]) for s in skipped], [("A", 5, 4)])
            row = result["entries"][0]
            self.assertEqual(row["statement_id"], keys[0][2])
            self.assertEqual(row["class"], "observed")
            self.assertFalse(row["payload"]["query_completed"])
            self.assertEqual(row["payload"]["note"], skipped[0]["diagnostic"])
            self.assertEqual(json.loads((directory / "validation.json").read_bytes())["receipt"]["skipped"], skipped)
            warm = prepare(repository, directory, membership, request, bound=4, cache=cache)
            self.assertEqual(warm["hits"], keys[1:])
            self.assertEqual(warm["execute"], [])
            replay, warm_record = run_batches(repository, directory, membership, request, warm,
                lambda *args, **kwargs: self.fail("warm candidate Environment ran"), "fixture-lean")
            self.assertEqual(replay, result)
            self.assertEqual(warm_record["receipt"], record["receipt"])

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
