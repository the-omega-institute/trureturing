"""Direct legacy byte addresses and semantic report inputs are distinct contracts."""
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from lean_seed_contract import INPUT, ROOT, REV, OTHER, PartitionFixture, digest, write


class PartitionTests(PartitionFixture, unittest.TestCase):
    def byte_manifest(self, paths):
        # Preimage read as data from 7bab46b34852aa352dd437f088c6183db0c537bf;
        # expectations hash candidate fixture bytes, never execute historical code.
        return digest(b"".join(
            (digest((self.root / path).read_bytes()) + "  " + path + "\n").encode("utf-8")
            for path in paths))

    def address(self, command="address"):
        result = self.run_input(command)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertRegex(result.stdout, r"^[0-9a-f]{64}( [0-9a-f]{64})?\n$")
        return result.stdout.strip()

    def semantic_input(self):
        with tempfile.TemporaryDirectory() as scratch:
            result = subprocess.run(["bash", "-euo", "pipefail", "-c", '''
REPOSITORY="$1"
TMP_ROOT="$2"
source "$3"
lean_cache_address
''', "semantic-input", str(self.root), scratch, str(INPUT)], text=True, capture_output=True)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertRegex(result.stdout, r"^[0-9a-f]{64} [0-9a-f]{64}\n$")
        return result.stdout.split()

    def test_legacy_dependency_address_hashes_only_pinned_file_bytes(self):
        paths = ["lean-toolchain", "lake-manifest.json"]
        before = self.address("dependency-address")
        self.assertEqual(self.byte_manifest(paths), before)
        write(self.root / "D5/A.lean", "def a := 2\n")
        write(self.root / "lakefile.toml", 'keywords = ["metadata"]\n')
        write(self.root / "lakefile.lean", "-- executable configuration\n")
        self.assertEqual(before, self.address("dependency-address"))
        self.manifest["packages"][0]["inputRev"] = "new-requested-ref"
        self.save_manifest()
        changed = self.address("dependency-address")
        self.assertEqual(self.byte_manifest(paths), changed)
        self.assertNotEqual(before, changed)
        write(self.root / "lean-toolchain", "different-toolchain\n")
        self.assertEqual(self.byte_manifest(paths), self.address("dependency-address"))
        self.assertNotEqual(changed, self.address("dependency-address"))

    def test_legacy_project_address_hashes_candidate_manifest_bytes(self):
        for path in ["D5/Z.lean", "D5/nested/B.lean", "tools/lean-inspector/Z.lean",
                     "tools/lean-inspector/A.lean"]:
            write(self.root / path, "-- " + path + "\n")
        sources = ["Trureturing.lean", "D5/A.lean", "D5/Z.lean", "D5/nested/B.lean",
                   "tools/lean-inspector/A.lean", "tools/lean-inspector/Z.lean"]
        for lakefiles in [["lakefile.toml"], ["lakefile.toml", "lakefile.lean"], ["lakefile.lean"]]:
            with self.subTest(lakefiles=lakefiles):
                if "lakefile.lean" in lakefiles:
                    write(self.root / "lakefile.lean", "-- executable configuration\n")
                if "lakefile.toml" not in lakefiles:
                    (self.root / "lakefile.toml").unlink()
                expected = self.byte_manifest(sources) + " " + self.byte_manifest(
                    ["lean-toolchain", "lake-manifest.json", *lakefiles])
                self.assertEqual(expected, self.address())

    def test_legacy_project_config_tracks_metadata_bytes(self):
        before = self.address().split()
        self.manifest["version"] = "new-metadata"
        self.save_manifest()
        write(self.root / "lakefile.toml", 'name = "renamed"\nkeywords = ["metadata"]\n[leanOptions]\nmaxRecDepth = 1000\n')
        after = self.address().split()
        self.assertEqual(before[0], after[0])
        self.assertNotEqual(before[1], after[1])
        self.assertEqual(self.byte_manifest(["lean-toolchain", "lake-manifest.json", "lakefile.toml"]), after[1])

    def test_legacy_inputs_fail_without_required_files(self):
        for command, paths in [("dependency-address", ["lean-toolchain", "lake-manifest.json"]),
                               ("address", ["lean-toolchain", "lake-manifest.json", "lakefile.toml", "Trureturing.lean"])]:
            for relative in paths:
                with self.subTest(command=command, missing=relative):
                    path = self.root / relative
                    before = path.read_bytes()
                    path.unlink()
                    try:
                        result = self.run_input(command)
                        self.assertEqual(2, result.returncode, result.stdout + result.stderr)
                        self.assertEqual("", result.stdout)
                    finally:
                        path.write_bytes(before)

    def test_partition_uses_exactly_resolved_mathlib(self):
        self.assertEqual(REV, self.partition())
        self.manifest["packages"][0]["inputRev"] = "another-tag"
        self.manifest["version"] = "metadata"
        self.save_manifest()
        write(self.root / "lean-toolchain", "different spelling\n")
        write(self.root / "D5/A.lean", "def a := 2\n")
        write(self.root / "lakefile.toml", 'keywords = ["different"]\n')
        self.assertEqual(REV, self.partition())
        self.manifest["packages"][0]["rev"] = OTHER
        self.save_manifest()
        self.assertEqual(OTHER, self.partition())

    def test_missing_duplicate_and_unresolved_mathlib_are_invalid(self):
        for packages in [[], [{"name": "mathlib", "inputRev": REV}],
                         [{"name": "mathlib", "rev": "v4.33.0"}],
                         [{"name": "mathlib", "rev": REV}] * 2]:
            self.manifest["packages"] = packages
            self.save_manifest()
            result = self.run_input("partition")
            self.assertEqual(2, result.returncode, result.stdout + result.stderr)
            self.assertEqual("", result.stdout)

    def test_actions_snapshots_share_partition_and_pr_cannot_save(self):
        def keys(run, attempt, event, ref, success="true"):
            environment = {"GITHUB_RUN_ID": run, "GITHUB_RUN_ATTEMPT": attempt,
                           "GITHUB_EVENT_NAME": event, "GITHUB_REF": ref,
                           "STRATALINT_CHECK_SUCCEEDED": success}
            result = subprocess.run([sys.executable, str(ROOT / "tools/scripts/worktree/lean_actions.py"),
                                     "keys", "--repository", str(self.root)],
                                    text=True, capture_output=True,
                                    env={**os.environ, **environment})
            self.assertEqual(0, result.returncode, result.stderr)
            flat = dict(line.split("=", 1) for line in result.stdout.splitlines())
            flat["save_allowed"] = flat["save_allowed"] == "true"
            return {**flat, **{
                layer: {"restore_prefix": flat[layer + "_restore_prefix"],
                        "key": flat[layer + "_key"], "path": flat[layer + "_path"]}
                for layer in ("dependency", "project", "report")}}
        first = keys("12", "1", "push", "refs/heads/dev")
        self.manifest["packages"].append({"name": "other", "rev": OTHER})
        self.manifest["packages"][0]["inputRev"] = "another-tag"
        self.save_manifest()
        write(self.root / "lean-toolchain", "changed\n")
        write(self.root / "lakefile.toml", '[leanOptions]\nmaxRecDepth = 2000\n')
        write(self.root / "D5/A.lean", "def a := 2\n")
        second = keys("13", "2", "pull_request_target", "refs/heads/dev")
        self.assertTrue(first["save_allowed"])
        self.assertFalse(second["save_allowed"])
        self.assertFalse(keys("14", "1", "push", "refs/heads/dev", "false")["save_allowed"])
        self.manifest["packages"][0]["rev"] = OTHER
        self.save_manifest()
        upgraded = keys("15", "1", "push", "refs/heads/dev")
        self.assertEqual(first["release_prefix"], second["release_prefix"])
        self.assertNotEqual(first["release_prefix"], upgraded["release_prefix"])
        for layer in ["dependency", "project", "report"]:
            a, b = first[layer], second[layer]
            self.assertEqual(a["restore_prefix"], b["restore_prefix"])
            self.assertIn(REV, a["restore_prefix"])
            self.assertTrue(a["key"].endswith("12-1"))
            self.assertTrue(b["key"].endswith("13-2"))
            self.assertNotEqual(a["key"], b["key"])
            self.assertNotEqual(a["restore_prefix"], upgraded[layer]["restore_prefix"])

    def test_binary_platform_isolates_all_seed_layers(self):
        sys.path.insert(0, str(ROOT / "tools/scripts/worktree"))
        import lean_cache
        spec = importlib.util.spec_from_file_location("lean_actions", ROOT / "tools/scripts/worktree/lean_actions.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        for system, machine, expected in [("Linux", "x86_64", "linux-x64"),
                                          ("Linux", "aarch64", "linux-arm64"),
                                          ("Darwin", "arm64", "darwin-arm64")]:
            with self.subTest(platform=expected), \
                    mock.patch.object(lean_cache.platform, "system", return_value=system), \
                    mock.patch.object(lean_cache.platform, "machine", return_value=machine), \
                    mock.patch.dict(os.environ, GITHUB_RUN_ID="12", GITHUB_RUN_ATTEMPT="1"):
                keys = module.actions_keys(self.root)
                self.assertEqual(f"{REV}/{expected}", keys["partition"])
                self.assertEqual(f"lean-cache-v2-{REV}-{expected}-", keys["release_prefix"])
                for layer in ["dependency", "project", "report"]:
                    prefix = f"lean-{layer}-v3-{REV}-{expected}-"
                    self.assertEqual(prefix, keys[layer]["restore_prefix"])
                    self.assertEqual(prefix + "12-1", keys[layer]["key"])

    def test_metadata_has_no_semantic_config_effect(self):
        before = self.semantic_input()
        self.manifest["version"] = "new-metadata"
        self.manifest["packages"][0]["inputRev"] = "same-resolved"
        self.save_manifest()
        write(self.root / "lakefile.toml", 'name = "renamed"\nkeywords = ["metadata"]\n[leanOptions]\nmaxRecDepth = 1000\n')
        self.assertEqual(before, self.semantic_input())
        write(self.root / "lakefile.toml", '[leanOptions]\nmaxRecDepth = 2000\n')
        changed = self.semantic_input()
        self.assertEqual(before[0], changed[0])
        self.assertNotEqual(before[1], changed[1])

    def test_source_changes_only_the_source_report_input(self):
        before = self.semantic_input()
        write(self.root / "D5/A.lean", "def a := 2\n")
        changed = self.semantic_input()
        self.assertNotEqual(before[0], changed[0])
        self.assertEqual(before[1], changed[1])


if __name__ == "__main__":
    unittest.main(verbosity=2)
