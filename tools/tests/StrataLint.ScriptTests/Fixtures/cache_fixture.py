"""Shared isolated repository and Actions cache inputs for native fixture suites."""
import json
import os
import pathlib
import subprocess
import sys
import tempfile

REPO = pathlib.Path(__file__).resolve().parents[4]
CI = REPO / "tools/scripts/workflow/ci.py"
CACHE = REPO / "tools/scripts/worktree/lean_actions.py"
REV = "a" * 40


class CacheFixture:
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ci-contract-")
        self.root = pathlib.Path(self.temp.name)
        self.env = dict(os.environ, GITHUB_RUN_ID="17", GITHUB_RUN_ATTEMPT="2",
                        GITHUB_EVENT_NAME="push", GITHUB_REF="refs/heads/dev",
                        CI_WORKFLOW_INPUTS="", GITHUB_EVENT_PATH="",
                        STRATALINT_CHECK_SUCCEEDED="true", STRATALINT_CACHE_WRITES="true",
                        HOME=str(self.root),
                        GITHUB_OUTPUT=str(self.root / "outputs"), GITHUB_ENV=str(self.root / "environment"))
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "rev": REV}]}))
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")

    def tearDown(self):
        self.temp.cleanup()

    def run_tool(self, script, *args, env=None):
        return subprocess.run([sys.executable, str(script), *args, "--repository", str(self.root)],
                              env=env or self.env, capture_output=True, text=True)

    def snapshot_result(self):
        (self.root / "outputs").unlink(missing_ok=True)
        result = self.run_tool(CACHE, "snapshot")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        readiness = dict(line.split("=", 1) for line in (self.root / "outputs").read_text().splitlines())
        receipts = {entry["layer"]: entry for entry in (
            json.loads(line.removeprefix("LEAN_ACTIONS_CACHE "))
            for line in result.stdout.splitlines() if line.startswith("LEAN_ACTIONS_CACHE "))}
        return readiness, receipts

    def dependency_files(self):
        source = self.root / ".lake/packages"
        material = {
            "mathlib/scripts/bench/size/run": (b"#!/bin/sh\nprintf 'size\\n'\n", 0o755),
            "mathlib/scripts/bench/build/fake-root/bin/lean": (b"#!/bin/sh\nexit 0\n", 0o755),
            "batteries/README.md": (b"# Batteries\n\x00private bytes\xff\n", 0o640),
        }
        for relative, (data, mode) in material.items():
            path = source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(mode)
        return source, material
