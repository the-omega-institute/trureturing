"""Analysis caller contracts with the compiled ensure owner and private inputs."""
import json
import os
import pathlib
import shutil
import subprocess
import unittest

import lean_seed_contract
from lean_seed_support import ROOT, write


class AnalysisCacheTests(unittest.TestCase):
    def setUp(self):
        self.transport = lean_seed_contract.TransportTests("test_optional_fetch_valid_seed_still_reaches_build")
        self.transport.setUp()
        self.addCleanup(self.transport.doCleanups)
        self.root = self.transport.root
        self.transport.manifest["packages"][0].update({
            "type": "git", "url": "https://example.invalid/mathlib.git", "subDir": None,
            "configFile": "lakefile.lean", "manifestFile": "lake-manifest.json"})
        self.transport.save_manifest()
        for arguments in (("init", "-q"), ("add", "lake-manifest.json", "lakefile.toml", "lean-toolchain", "Trureturing.lean", "D5"),
                ("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "analysis fixture")):
            subprocess.run(["git", "-C", str(self.root), *arguments], check=True, capture_output=True)
        self.bin = self.transport.bin
        self.producer = pathlib.Path(os.environ["ANALYSIS_TEST_PRODUCER"])
        self.assertTrue(self.producer.is_file(), str(self.producer))
        self.dotnet = shutil.which("dotnet")
        self.assertIsNotNone(self.dotnet)
        self.runner = self.root / "tools/lean-inspector/LeanInformationAuditAnalysis/run-analysis-fixtures.sh"
        self.runner.parent.mkdir(parents=True)
        shutil.copy2(ROOT / self.runner.relative_to(self.root), self.runner)
        for name in ("CausalProjection", "BoundedClosure"):
            write(self.runner.with_name(name + ".lean"), "-- private analysis input\n")
        write(self.runner.parent.parent / "LeanInformationAuditRegAnalysis/FrozenRootAnalysis.lean",
              "-- downstream production analysis input\n")
        write(self.root / "Reg/lakefile.toml", 'name = "reg"\n')
        packages = [dict(row, inherited=True) for row in self.transport.manifest["packages"]]
        packages.extend({"type": "path", "name": name, "dir": directory,
                         "configFile": config, "manifestFile": "lake-manifest.json", "inherited": False}
                        for name, directory, config in (
                            ("trureturing", "..", "lakefile.toml"),
                            ("leanInspectorInterface", "../tools/lean-inspector-interface", "lakefile.toml"),
                            ("leanInspector", "../tools/lean-inspector", "lakefile.lean")))
        write(self.root / "Reg/lake-manifest.json",
              json.dumps({"packagesDir": "../.lake/packages", "packages": packages}))
        for name in ("lean-cache-run.sh", "lean-cache-ensure.sh", "lean-cache-publish.sh", "lean_cache_release.py", "lean_cache.py"):
            target = self.root / "tools/scripts/worktree" / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / target.relative_to(self.root), target)
        shutil.copy2(ROOT / "Makefile", self.root / "Makefile")
        self.output = self.root / "output/artifacts"

    def prepare(self, seed="absent"):
        if seed in ("valid", "corrupt"):
            published = self.transport.transport("publish")
            self.assertEqual(0, published.returncode, published.stdout + published.stderr)
            if seed == "corrupt":
                for archive in self.transport.remote.glob("*/lean-build.tgz"):
                    write(archive, "corrupt transfer")
        shutil.rmtree(self.root / ".lake")
        (self.bin / "make").unlink()
        write(self.bin / "dotnet", DOTNET_LAUNCHER)
        write(self.bin / "lake", LAKE)
        for name in ("dotnet", "lake"):
            (self.bin / name).chmod(0o755)
        if seed == "timeout":
            # Inject the transport's actual exception type without a wall-clock
            # verdict. The owner's real process deadline has its own fixture.
            write(self.bin / "sitecustomize.py", """
import subprocess
original = subprocess.run
def run(args, *rest, **kwargs):
    if args[0] == "gh":
        raise subprocess.TimeoutExpired(args, 0)
    return original(args, *rest, **kwargs)
subprocess.run = run
""")

    def run_analysis(self, scope="all", **extra):
        environment = self.transport.transport_environment(
            ANALYSIS_REAL_DOTNET=self.dotnet, ANALYSIS_TEST_PRODUCER=str(self.producer),
            STRATALINT_LEAN_PRODUCER_DLL=str(self.producer),
            LAKE_BIN=str(self.bin / "lake"), PYTHONPATH=str(self.bin),
            STRATALINT_LEAN_CACHE_DONORS="", XDG_CACHE_HOME=str(self.root / "cache"),
            # This synthetic fixture deliberately has no real Lean artifacts.
            STRATALINT_ACCEPT_COLD_BUILD="1",
            STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS="300", **extra)
        result = subprocess.run(["bash", "-euo", "pipefail", "-c", '''
mkdir -p "$1/output"
"$2" "$1/output/artifacts" "$3" 2>&1 | tee "$1/output/run.log"
''', "analysis-caller", str(self.root), str(self.runner), scope], cwd=self.root,
            text=True, capture_output=True, env=environment)
        print(result.stdout, end="")
        print(result.stderr, end="")
        return result

    def assert_produced(self, result, archive_status):
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        receipts = [json.loads(line.removeprefix("LEAN_CACHE "))
                    for line in result.stdout.splitlines() if line.startswith("LEAN_CACHE ")]
        self.assertEqual(3, len(receipts), result.stdout)
        self.assertEqual(archive_status, receipts[0]["archive_status"])
        self.assertEqual(["build LeanInformationAuditAnalysis",
                          f"-d {self.root.resolve()}/Reg build @reg/LeanInformationAuditRegAnalysis"],
                         [line for line in (self.root / "lake-runs").read_text().splitlines()
                          if line != "exe cache get"])
        self.assertEqual(7, len(list(self.output.iterdir())))
        self.assertIn("ANALYSIS_FIXTURES_EXIT=0", result.stdout)

    def test_absent_seed_reaches_analysis(self):
        self.prepare()
        self.assert_produced(self.run_analysis(), "miss")

    def test_corrupt_seed_reaches_analysis(self):
        self.prepare("corrupt")
        result = self.run_analysis()
        self.assert_produced(result, "miss")
        self.assertIn("transferred asset digest mismatch", result.stdout)
        self.assertFalse((self.root / ".lake/build/lib/lean/D5/A.olean").exists())

    def test_timed_out_seed_reaches_analysis(self):
        self.prepare("timeout")
        result = self.run_analysis()
        self.assert_produced(result, "miss")
        self.assertIn("timed out", result.stdout)

    def test_valid_seed_is_only_a_starting_point(self):
        self.prepare("valid")
        self.assert_produced(self.run_analysis(), "unpacked")
        self.assertEqual("locally-produced-olean",
                         (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())

    def test_real_analysis_failure_survives_seed_and_tee(self):
        self.prepare("valid")
        result = self.run_analysis(ANALYSIS_BUILD_EXIT="19")
        self.assertEqual(2, result.returncode, result.stdout + result.stderr)
        self.assertIn('"archive_status":"unpacked"', result.stdout)
        self.assertIn("ANALYSIS_FIXTURES_EXIT=2", result.stdout)
        self.assertIn("Error 19", result.stdout)
        self.assertEqual(["exe cache get", "build LeanInformationAuditAnalysis"],
                         (self.root / "lake-runs").read_text().splitlines())
        self.assertEqual([], list(self.output.iterdir()))

    def test_dependency_transfer_failure_reaches_analysis(self):
        self.prepare()
        result = self.run_analysis(ANALYSIS_DEPENDENCY_EXIT="23")
        self.assert_produced(result, "not_attempted")
        self.assertIn('"status":"degraded"', result.stdout)

    def test_preparation_failure_stops_before_analysis(self):
        self.prepare()
        write(self.root / ".lake", "not a directory")
        result = self.run_analysis()
        self.assertNotEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn(".lake exists but is not a directory", result.stdout)
        self.assertNotIn("ANALYSIS_FIXTURES_EXIT=0", result.stdout)
        self.assertFalse((self.root / "lake-runs").exists())

    def test_dotnet_launch_failure_stops_before_analysis(self):
        self.prepare()
        result = self.run_analysis(ANALYSIS_DOTNET_EXIT="29")
        self.assertNotEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertNotIn("ANALYSIS_FIXTURES_EXIT=0", result.stdout)
        self.assertFalse((self.root / "lake-runs").exists())


    def test_production_scope_uses_reg_and_only_clears_its_export_trace(self):
        self.prepare()
        generic = self.root / ".lake/build/lib/lean/LeanInformationAuditAnalysis/CausalProjection.trace"
        production = self.root / ".lake/build/reg/lib/lean/LeanInformationAuditRegAnalysis/FrozenRootAnalysis.trace"
        write(generic, "generic trace")
        write(production, "production trace")
        result = self.run_analysis(scope="production")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual("generic trace", generic.read_text())
        self.assertFalse(production.exists())
        runs = (self.root / "lake-runs").read_text().splitlines()
        self.assertEqual([f"-d {self.root.resolve()}/Reg build @reg/LeanInformationAuditRegAnalysis"],
                         [line for line in runs if line != "exe cache get"])
        self.assertEqual({"frozen-seal.json", "frozen-analysis.json", "frozen-analysis.txt"},
                         {path.name for path in self.output.iterdir()})

    def test_reg_analysis_failure_reaches_runner_exit(self):
        self.prepare()
        result = self.run_analysis(scope="production", ANALYSIS_BUILD_EXIT="19")
        self.assertEqual(2, result.returncode, result.stdout + result.stderr)
        self.assertIn("Error 19", result.stdout)
        self.assertIn("ANALYSIS_FIXTURES_EXIT=2", result.stdout)
        self.assertEqual([], list(self.output.iterdir()))


# Keep the real make recipe and shell entrypoint, with the compiled leaf producer.
DOTNET_LAUNCHER = '''#!/usr/bin/env bash
set -euo pipefail
[[ "$#" -ge 2 && "$1" == "$ANALYSIS_TEST_PRODUCER" && ( "$2" == ensure-cache || "$2" == with-cache-reader ) ]] || exit 86
if [[ -n "${ANALYSIS_DOTNET_EXIT:-}" ]]; then exit "$ANALYSIS_DOTNET_EXIT"; fi
exec "$ANALYSIS_REAL_DOTNET" "$@"
'''

LAKE = '''#!/usr/bin/env python3
import os, pathlib, sys
root = pathlib.Path.cwd()
args = sys.argv[1:]
with (root / "lake-runs").open("a") as log: log.write(" ".join(args) + "\\n")
if args == ["exe", "cache", "get"]:
    (root / ".lake/packages").mkdir(parents=True, exist_ok=True)
    sys.exit(int(os.environ.get("ANALYSIS_DEPENDENCY_EXIT", "0")))
if args == ["build", "LeanInformationAuditAnalysis"]:
    artifacts = ("causal-analysis.json", "causal-analysis.txt", "bounded-analysis.json", "bounded-analysis.txt")
else:
    assert args == ["-d", str(root / "Reg"), "build", "@reg/LeanInformationAuditRegAnalysis"], args
    artifacts = ("frozen-seal.json", "frozen-analysis.json", "frozen-analysis.txt")
failure = int(os.environ.get("ANALYSIS_BUILD_EXIT", "0"))
if failure: sys.exit(failure)
output = pathlib.Path(os.environ["IE_PROJECTION_OUTPUT_DIR"])
for name in artifacts:
    (output / name).write_text("analysis-produced\\n")
'''


if __name__ == "__main__":
    unittest.main(verbosity=2)
