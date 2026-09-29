"""Actual Census dependency walks using both caller environments on a warm tree."""

import argparse
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import pipeline
from native import build
from negative_fixtures import lean_env
from phases import read, write


class NativeEnvironmentTests(unittest.TestCase):
    def setUp(self):
        self.repository = pathlib.Path(__file__).resolve().parents[4]
        self.temporary = tempfile.TemporaryDirectory(prefix="census native ")
        self.addCleanup(self.temporary.cleanup)
        self.directory = pathlib.Path(self.temporary.name)

    def production_env(self):
        report = self.directory / "truth.json"
        write(report, {"source_commit": "fixture-head", "nodes": [{
            "repo_path": "LeanInformationAudit/Tests/Census/Query/StreamingTarget.lean",
            "freeze_status": "frozen", "declarations": [{"kind": "theorem",
                "declaration_name_key": "ns(n0,6:target)", "statement_id": "sha256:" + "0" * 64}]}]})
        options = argparse.Namespace(output=str(self.directory / "pipeline"),
            fixture_truth_export=str(report), lean_report=str(report), prefix="LeanInformationAudit")
        captured = {}

        class NativeReached(Exception):
            pass

        def step(command, logs, label, **kwargs):
            # The outer fixture runner already did the warm canonical build.
            # Stop at the native boundary; Lake environment resolution is real.
            if label == "native_build":
                captured.update(kwargs["env"])
                raise NativeReached()
            self.assertIn(label, ("cache_ensure", "lake_freshness"))
            logs.mkdir(parents=True, exist_ok=True)
            (logs / (label + ".log")).write_text("")
            return {"wall_seconds": 0, "rss_budget_gib": None}

        with mock.patch("resources.run", side_effect=step), self.assertRaises(NativeReached):
            pipeline.execute(options)
        return captured

    def check_native(self, env):
        # build always asks Lean for the recursive source closure, even when
        # the native binary is already present. No dependency query is mocked.
        binaries = {}
        for program in ("scan.lean", "membership.lean"):
            with self.subTest(program=program):
                binaries[program] = build(self.repository, program, env)
        if len(binaries) != 2:
            return
        manifest, request = self.directory / "manifest.json", self.directory / "request.json"
        stream, result = self.directory / "stream.jsonl", self.directory / "membership.json"
        module = "LeanInformationAudit.Census.Ownership"
        olean = self.repository / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        parts = [olean, pathlib.Path(str(olean) + ".server"), pathlib.Path(str(olean) + ".private")]
        write(manifest, [[module, [str(path) for path in parts if path.is_file()]]])
        write(request, {"keys": [], "roots": [], "assignment": {},
                        "external_graph": [], "discovery_roots": []})
        for program, arguments in (("scan.lean", [manifest, request, stream]),
                                   ("membership.lean", [stream, request, result])):
            subprocess.run([str(binaries[program]), *map(str, arguments)],
                           cwd=self.repository, env=env, check=True)
        rows = [json.loads(line) for line in stream.read_text().splitlines()]
        self.assertTrue(rows)
        self.assertEqual({row["module"] for row in rows}, {module})
        self.assertEqual(read(result)["errors"], [])
        self.assertEqual(pathlib.Path(str(result) + ".rows.jsonl").read_bytes(), b"")
        # Bad native inputs still fail instead of yielding a successful query.
        for program in binaries:
            with self.subTest(invalid_arguments=program):
                rejected = subprocess.run([str(binaries[program])], cwd=self.repository,
                    env=env, text=True, capture_output=True)
                self.assertNotEqual(rejected.returncode, 0)
                self.assertIn("expected", rejected.stderr + rejected.stdout)

    def test_production_environment_builds_native_census(self):
        self.check_native(self.production_env())

    def test_fixture_environment_builds_native_census(self):
        self.check_native(lean_env(self.repository))


def check_native_environments():
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(NativeEnvironmentTests)
    if not unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful():
        raise AssertionError("Census native caller environments")


if __name__ == "__main__":
    unittest.main()
