"""Compare real Inspector output with its incremental merge on an Init-only Lake project."""
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

from lean_seed_support import ROOT, DELTA, digest, write


class NativeReportTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="native-report-")
        self.addCleanup(self.temporary.cleanup)
        self.root = pathlib.Path(self.temporary.name)
        self.producer = pathlib.Path(os.environ["NATIVE_REPORT_PRODUCER"])
        self.lake = shutil.which("lake")
        self.assertIsNotNone(self.lake)
        write(self.root / "lean-toolchain", (ROOT / "lean-toolchain").read_text())
        write(self.root / ".gitignore", ".lake/\nbuild/\n")
        write(self.root / "lakefile.toml", '''name = "snapshot_probe"
defaultTargets = ["D5"]
[[lean_lib]]
name = "D5"
globs = ["D5.+"]
''')
        self.paths = {"D5.S0.Carrier." + name: "D5/S0/Carrier/" + name + ".lean"
                      for name in ("Claim", "ClaimDependency", "Consumer", "Result", "Unrelated")}
        self.source("ClaimDependency", "def value : Nat := 1\n")
        self.source("Claim", "import D5.S0.Carrier.ClaimDependency\ndef claim : Prop := value = 2\n")
        self.source("Result", '''/- GID: D5/S0/Carrier/Result
   generality: I
   mirror-B: D5/B/S0/Carrier/Result
   mirror-E: none(waiver:pure-definition)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Carrier/Claim.claim; result=D5/S0/Carrier/Result.refute; claim=D5/S0/Carrier/Claim.claim
   digest: Synthetic refutation fixture. -/
theorem refute : Not (1 = (2 : Nat)) := by decide
''')
        self.source("Consumer", "import D5.S0.Carrier.Result\ntheorem consumer : Not (1 = (2 : Nat)) := refute\n")
        self.source("Unrelated", "def unrelated : Nat := 7\n")
        self.run_command("git", "init", "-q")
        self.cache = self.root / "build/cache"
        self.baseline = self.cache / ("a" * 64) / "raw-lean-report.json"
        # These identities hold the fixture's producer/configuration fixed; the
        # real executable-closure mutations are exercised by ProducerIsolationTests.
        self.identity = "b" * 64

    def source(self, name, text):
        write(self.root / self.paths["D5.S0.Carrier." + name], text)

    def run_command(self, *command, expected=0):
        result = subprocess.run(command, cwd=self.root, text=True, capture_output=True)
        self.assertEqual(expected, result.returncode, result.stdout + result.stderr)
        return result

    def build(self):
        result = self.run_command(self.lake, "build")
        # Lake's built lines are diagnostics; no elapsed time bears a verdict.
        return [line for line in (result.stdout + result.stderr).splitlines() if "Built " in line]

    def inspect(self, output, names):
        output.parent.mkdir(parents=True, exist_ok=True)
        utility = self.run_command("dotnet", str(self.producer), "lean-utility-input")
        obligations = json.loads(utility.stdout)
        self.assertEqual(1, len(obligations))
        write(self.root / "build/utility.json", utility.stdout)
        arguments = [self.lake, "env", "lean", "--run", str(ROOT / "tools/lean-inspector/Inspector.lean"),
                     "--output", str(output) + ".spool.json", "--material-spool", str(output) + ".spool",
                     "--utility-input", str(self.root / "build/utility.json")]
        for name in sorted(names):
            path = self.paths[name]
            arguments.extend([name, path, "sha256:" + digest((self.root / path).read_bytes())])
        self.run_command(*arguments)
        self.run_command(sys.executable, str(DELTA.with_name("materials.py")), "compact",
                         str(output) + ".spool.json", str(output) + ".spool", str(output))

    def seed(self):
        report_sha = digest(self.baseline.read_bytes())
        write(pathlib.Path(str(self.baseline) + ".sha256"), report_sha + "  raw-lean-report.json\n")
        write(pathlib.Path(str(self.baseline) + ".input.attestation"),
              "schema=stratalint-lean-report-input-attestation-v1\nrepository_input_sha256=" + self.identity
              + "\nproducer_sha256=" + self.identity + "\nreport_sha256=" + report_sha + "\n")
        write(pathlib.Path(str(self.baseline) + ".provenance.json"), json.dumps({
            "schema": "stratalint-lean-report-provenance-v1", "side": "candidate", "mode": "produced",
            "source_side": "candidate", "input_address": "sha256:" + self.identity,
            "producer_sha256": self.identity, "repository_inspector_sha256": self.identity,
            "lean_sources_sha256": self.identity, "lean_config_sha256": self.identity,
            "report_sha256": report_sha}))

    def plan(self):
        table = self.root / "build/modules.tsv"
        write(table, "".join(name + "\t" + path + "\n" for name, path in sorted(self.paths.items())
                            if (self.root / path).is_file()))
        plan = self.root / "build/plan.json"
        self.run_command(sys.executable, str(DELTA), "plan", str(self.root), str(self.cache),
                         *([self.identity] * 4), str(table), str(plan))
        value = json.loads(plan.read_text())
        self.assertIn(value["status"], ("reuse", "delta"))
        return plan, value["recheck"]

    def test_incremental_equals_full_and_metadata_rebuilds_nothing(self):
        self.build()
        self.inspect(self.baseline, self.paths)
        self.seed()
        self.assertTrue(next(module for module in json.loads(self.baseline.read_text())["modules"]
                             if module["module"].endswith(".Result"))["utility_refutation"]["is_closed_negation"])
        config = self.root / "lakefile.toml"
        write(config, config.read_text().replace('name = "snapshot_probe"',
                                               'keywords = ["metadata"]\nname = "snapshot_probe"'))
        self.assertEqual([], self.build())
        plan, selected = self.plan()
        self.assertEqual([], selected)
        print(json.dumps({"case": "native-metadata", "lean_built": 0, "selected": 0, "modules": 5}), flush=True)

        # The designated claim is deliberately outside Result's Lean imports.
        self.source("ClaimDependency", "def value : Nat := 1 + 0\n")
        built = self.build()
        plan, selected = self.plan()
        self.assertEqual(["D5.S0.Carrier." + name for name in
                          ("Claim", "ClaimDependency", "Consumer", "Result")], selected)
        subset, merged, full = (self.root / ("build/" + name + ".json") for name in ("subset", "merged", "full"))
        self.inspect(subset, selected)
        self.run_command(sys.executable, str(DELTA), "merge", str(plan), str(subset), str(merged))
        self.inspect(full, self.paths)
        self.assertEqual(full.read_bytes(), merged.read_bytes())
        self.assertEqual(pathlib.Path(str(full) + ".materials.zip").read_bytes(),
                         pathlib.Path(str(merged) + ".materials.zip").read_bytes())
        print(json.dumps({"case": "native-claim-dependency", "lean_built": len(built),
                          "selected": len(selected), "modules": 5, "report_and_materials_equal": True}), flush=True)

        (self.root / self.paths["D5.S0.Carrier.Claim"]).unlink()
        plan, selected = self.plan()
        self.assertIn("D5.S0.Carrier.Result", selected)
        result = self.run_command("dotnet", str(self.producer), "lean-utility-input", expected=2)
        self.assertIn("Refutation claim source is absent", result.stderr)
        print(json.dumps({"case": "native-deleted-claim", "selected": len(selected), "utility_exit": 2}), flush=True)


if __name__ == "__main__":
    unittest.main(verbosity=2)
