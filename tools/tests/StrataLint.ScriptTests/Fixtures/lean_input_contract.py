"""Mathlib-only cache partition and Actions snapshot transport identities."""
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from lean_seed_support import INPUT, ROOT, REV, OTHER, PartitionFixture, digest, write


class PartitionTests(PartitionFixture, unittest.TestCase):
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
            self.assertFalse(any(key.startswith("report_") for key in flat), flat)
            flat["save_allowed"] = flat["save_allowed"] == "true"
            return {**flat, **{
                layer: {"restore_prefix": flat[layer + "_restore_prefix"],
                        "key": flat[layer + "_key"], "path": flat[layer + "_path"]}
                for layer in ("dependency", "project")}}
        first = keys("12", "1", "push", "refs/heads/dev")
        self.manifest["packages"].append({"name": "other", "rev": OTHER})
        self.manifest["packages"][0]["inputRev"] = "another-tag"
        self.save_manifest()
        write(self.root / "lean-toolchain", "changed\n")
        write(self.root / "lakefile.toml", '[leanOptions]\nmaxRecDepth = 2000\n')
        write(self.root / "D5/A.lean", "def a := 2\n")
        second = keys("13", "2", "pull_request", "refs/heads/dev")
        self.assertTrue(first["save_allowed"])
        self.assertFalse(second["save_allowed"])
        self.assertFalse(keys("14", "1", "push", "refs/heads/dev", "false")["save_allowed"])
        self.manifest["packages"][0]["rev"] = OTHER
        self.save_manifest()
        upgraded = keys("15", "1", "push", "refs/heads/dev")
        self.assertEqual(first["release_prefix"], second["release_prefix"])
        self.assertNotEqual(first["release_prefix"], upgraded["release_prefix"])
        for layer in ["dependency", "project"]:
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
                for layer in ["dependency", "project"]:
                    prefix = f"lean-{layer}-v3-{REV}-{expected}-"
                    self.assertEqual(prefix, keys[layer]["restore_prefix"])
                    self.assertEqual(prefix + "12-1", keys[layer]["key"])



if __name__ == "__main__":
    unittest.main(verbosity=2)
