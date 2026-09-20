"""Relocate a bounded native Census package using the existing warm fixture owner."""

import json
import pathlib
import shutil
import sys
import unittest

INSPECTOR = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(INSPECTOR / "tests"))
from test_native_support import NativeTestSupport, ROOT


class NativeRelocationTests(NativeTestSupport, unittest.TestCase):
    def test_census_callers_in_relocated_package_with_spaces(self):
        shutil.copytree(ROOT / "tools/lean-inspector-interface", self.root / "declaration package",
                        ignore=shutil.ignore_patterns(".lake", "__pycache__"))
        shutil.copytree(INSPECTOR / "Census", self.root / "tools/lean-inspector/Census",
                        ignore=shutil.ignore_patterns("__pycache__"))
        for name in ("NameWire", "Census/Ownership", "Census/Stream", "Census/Membership"):
            self.copy("tools/lean-inspector/LeanInformationAudit/" + name + ".lean")
        # Keep the support fixture's synthetic driver in this library's source root.
        (self.root / "LeanInformationAudit/Registry.lean").rename(
            self.root / "tools/lean-inspector/LeanInformationAudit/Registry.lean")
        (self.root / "LeanInformationAudit").rmdir()
        policy = self.root / "lean-report-inputs.json"
        policy.write_text(policy.read_text().replace('"LeanInformationAudit/Registry.lean"',
            '"tools/lean-inspector/LeanInformationAudit/Registry.lean"'))
        # This fixture puts the same dependency under a different source root.
        # Only Lake knows that location; Census cannot name it as a special case.
        config = self.root / "declaration package/lakefile.toml"
        config.write_text(config.read_text().replace('"../../.lake/', '"../.lake/'))
        config = self.root / "lakefile.toml"
        config.write_text(config.read_text().replace('name = "LeanInformationAudit"\n',
            'name = "LeanInformationAudit"\nsrcDir = "tools/lean-inspector"\n') +
            '\n[[require]]\nname = "leanInspectorInterface"\npath = "declaration package"\n')
        manifest = json.loads((self.root / "lake-manifest.json").read_text())
        manifest["packages"].append(dict(type="path", scope="", name="leanInspectorInterface",
            manifestFile="lake-manifest.json", inherited=False, dir="declaration package",
            configFile="lakefile.toml"))
        self.write("lake-manifest.json", json.dumps(manifest))
        self.ensure()
        command = ["make", "lean", "LEAN_TARGETS=LeanInformationAudit.Census.Stream "
                   "LeanInformationAudit.Census.Membership"]
        result = self.guarded_command(command, cwd=self.root, env=self.env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        donor = self.root
        destination = donor / "relocated census with spaces"
        destination.mkdir()
        for child in list(donor.iterdir()):
            if child == destination:
                continue
            if child.is_dir():
                shutil.copytree(child, destination / child.name)
            else:
                shutil.copy2(child, destination / child.name)
        original_env = self.env
        self.root = destination
        self.env = {key: value.replace(str(donor), str(destination))
                    for key, value in original_env.items()}
        try:
            # Revalidate the relocated warm inputs through the canonical make owner.
            result = self.guarded_command(command, cwd=self.root, env=self.env)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            result = self.guarded_command([sys.executable,
                "tools/lean-inspector/Census/tests/native_fixtures.py", "-v"],
                cwd=self.root, env=self.env)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Ran 2 tests", result.stderr)
        finally:
            self.root, self.env = donor, original_env


if __name__ == "__main__":
    unittest.main()
