"""The structural reader uses Inspector's self-contained dependency semantics."""

import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest

from negative_fixtures import lean_env, name_key
from phases import write


class StructureInspectorTests(unittest.TestCase):
    def setUp(self):
        self.repository = pathlib.Path(__file__).resolve().parents[4]
        self.env = lean_env(self.repository)
        self.lean = shutil.which("lean", path=self.env["PATH"])
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.folder = pathlib.Path(self.scratch.name)
        self.manifest, self.raw = self.folder / "manifest.json", self.folder / "raw.jsonl"
        module = "LeanInformationAudit.Tests.Census.Structure.Terms"
        olean = self.repository / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        write(self.manifest, [[module, [str(olean)]]])

    def test_standalone_inspector_owns_value_and_type_dependencies(self):
        # Give the standalone Inspector only the toolchain search path. The
        # fixture olean is input data, not an imported project module.
        env = dict(self.env, LEAN_PATH="")
        result = subprocess.run([self.lean, "--run", "tools/lean-inspector/Inspector.lean",
                                 "--dependencies", str(self.manifest), str(self.raw), "bodies"],
                                cwd=self.repository, env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, "inspectorDependencyOwner: " + result.stdout + result.stderr)
        declarations = {r["name"]: r for r in map(json.loads, self.raw.read_text().splitlines()) if "name" in r}
        named = lambda n: name_key("LeanInformationAudit.Tests.Census.Structure." + n)
        self.assertEqual(declarations[named("b")]["value"], [named("h")], "inspectorDependencyOwner")
        self.assertEqual(declarations[named("a")]["value"], [], "inspectorDependencyOwner")
        self.assertEqual(declarations[named("fixtureAxiom")]["type"], [name_key("True")],
                         "inspectorDependencyOwner")
        self.assertIsNone(declarations[named("fixtureAxiom")]["value"], "inspectorDependencyOwner")

    def test_structural_reader_propagates_inspector_failure(self):
        from native import build
        binary = build(self.repository, "structure.lean", self.env)
        fake = self.folder / "lean"
        fake.write_text("#!/bin/sh\nprintf 'inspector-fixture-failure\\n' >&2\nexit 47\n")
        fake.chmod(0o755)
        env = dict(self.env, PATH=str(self.folder) + os.pathsep + self.env["PATH"])
        result = subprocess.run([str(binary), str(self.manifest), str(self.raw), "bodies"],
                                cwd=self.repository, env=env, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0, "inspectorSubprocessFailurePropagation")
        self.assertIn("inspector-fixture-failure", result.stderr, "inspectorSubprocessFailurePropagation")


if __name__ == "__main__":
    unittest.main()
