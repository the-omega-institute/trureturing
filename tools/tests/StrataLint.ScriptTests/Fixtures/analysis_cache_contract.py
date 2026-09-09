"""Analysis caller contracts with the compiled ensure owner and private inputs."""
import json
import os
import pathlib
import shutil
import subprocess
import unittest

import lean_seed_contract
from lean_seed_contract import ROOT, write


class CurrentCacheTests(unittest.TestCase):
    def test_compiled_preparation_and_incremental_report_preserve_every_seed_outcome(self):
        seeds = ("actions", "actions-corrupt", "release", "release-corrupt", "miss", "transport")
        selected = os.environ.get("ANALYSIS_SEED_CASE")
        if selected:
            self.assertIn(selected, seeds)
            seeds = (selected,)
        for seed in seeds:
            with self.subTest(seed=seed):
                fixture = lean_seed_contract.InspectorTests("test_inspector_runs_lake_on_exact_seed_with_zero_reinspection")
                fixture.setUp()
                self.addCleanup(fixture.doCleanups)
                root = fixture.root
                write(root / ".gitignore", (ROOT / ".gitignore").read_text() + "remote/\nout/\ncache/\n")
                subprocess.run(["git", "init", "-q", str(root)], check=True)
                runtime = root / "bin"
                runtime.mkdir()
                remote = root / "remote"
                remote.mkdir()
                cli = pathlib.Path(os.environ["ANALYSIS_TEST_CLI"])
                self.assertTrue(cli.is_file(), str(cli))
                write(runtime / "dotnet", '''#!/usr/bin/env bash
set -euo pipefail
if [[ "$1" == msbuild ]]; then exec "$ANALYSIS_REAL_DOTNET" "$@"; fi
if [[ "$#" == 2 && "$1" == "$STRATALINT_LEAN_PRODUCER_DLL" && "$2" == lean-utility-input ]]; then
  exec "$ANALYSIS_REAL_DOTNET" "$@"
fi
[[ "$#" -ge 4 && "$1" == "$STRATALINT_LEAN_PRODUCER_DLL" &&
   "$2" == lean-cache-writer && "$3" == -- ]] || exit 86
exec "$ANALYSIS_REAL_DOTNET" "$STRATALINT_LEAN_PRODUCER_DLL" lean-cache-writer --path "$PWD" -- "${@:4}"
''')
                write(runtime / "make", "#!/bin/sh\nexit 0\n")
                write(runtime / "gh", lean_seed_contract.FAKE_GH.replace("args = sys.argv[1:]",
                    'args = sys.argv[1:]\nwith pathlib.Path(os.environ["GH_CALLS"]).open("a") as log: log.write(" ".join(args) + "\\n")'))
                for path in runtime.iterdir():
                    path.chmod(0o755)
                shutil.copy2(ROOT / "tools/scripts/worktree/lean-cache-run.sh",
                             root / "tools/scripts/worktree/lean-cache-run.sh")
                # The runtime stub still has an explicit source project for
                # compiler-owned producer discovery through its DLL entrypoint.
                write(root / "global.json", "{}\n")
                write(root / "producer.props", "<Project />\n")
                write(root / "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
                      '<Project><Import Project="../../producer.props" />'
                      '<ItemGroup><Compile Include="Fixture.cs" /></ItemGroup></Project>\n')
                write(root / "tools/StrataLint.EngineeringScope/Fixture.cs", "internal class Fixture { }\n")
                lake = lean_seed_contract.FAKE_LAKE.replace('if args == ["build"]:', '''if args == ["exe", "cache", "get"]:
    (root / ".lake/packages").mkdir(parents=True, exist_ok=True)
    sys.exit(0)
if args == ["build"]:
    if not os.environ.get("LAKE_BUILD_FAIL"):
        target = root / ".lake/build/lib/lean/D5/A.olean"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("current build output")''')
                write(fixture.lake, lake)
                env = dict(os.environ, PATH=str(runtime) + os.pathsep + os.environ["PATH"],
                    HOME=str(root), XDG_CACHE_HOME=str(root / "cache"), STRATALINT_LEAN_CACHE_DONORS="",
                    STRATALINT_ACTIONS_CACHE_SEEDED="", STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS="300",
                    ANALYSIS_REAL_DOTNET=shutil.which("dotnet"), ANALYSIS_TEST_CLI=str(cli),
                    STRATALINT_LEAN_PRODUCER_DLL=str(cli.with_name("StrataLint.EngineeringScope.dll")),
                    FAKE_REMOTE=str(remote), GH_CALLS=str(root / "gh-calls"),
                    GITHUB_SHA="d" * 40, GITHUB_RUN_ID="17", GITHUB_RUN_ATTEMPT="2",
                    GITHUB_EVENT_NAME="push", GITHUB_REF="refs/heads/dev", STRATALINT_CHECK_SUCCEEDED="true",
                    STRATALINT_CACHE_WRITES="true", GITHUB_ENV=str(root / "environment"), GITHUB_OUTPUT=str(root / "outputs"))
                write(root / ".lake/build/lib/lean/D5/A.olean", "previous build output")
                key = ""
                if seed.startswith("actions"):
                    snapshot = subprocess.run(["python3", str(ROOT / "tools/scripts/worktree/lean_actions.py"),
                        "snapshot", "--repository", str(root)], env=env, capture_output=True, text=True)
                    self.assertEqual(0, snapshot.returncode, snapshot.stdout + snapshot.stderr)
                    manifest = root / "build/lean-cache/project/manifest.json"
                    key = json.loads(manifest.read_text())["key"]
                    if seed == "actions-corrupt":
                        write(manifest.parent / "data/lib/lean/D5/A.olean", "corrupt")
                elif seed != "miss":
                    published = subprocess.run(["bash", str(ROOT / "tools/scripts/worktree/lean-cache-publish.sh"),
                        "publish", "--repository", str(root)], env=dict(env, GITHUB_EVENT_NAME="schedule"),
                        capture_output=True, text=True)
                    self.assertEqual(0, published.returncode, published.stdout + published.stderr)
                    if seed == "release-corrupt":
                        for archive in remote.glob("*/lean-build.tgz"):
                            write(archive, "corrupt")
                    if seed == "transport":
                        env["FAKE_FAIL"] = "download"
                shutil.rmtree(root / ".lake")
                (root / "gh-calls").unlink(missing_ok=True)
                restored = subprocess.run(["python3", str(ROOT / "tools/scripts/worktree/lean_actions.py"),
                    "restore", "--repository", str(root), "--project-key", key], env=env, capture_output=True, text=True)
                self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
                env.update(dict(line.split("=", 1) for line in (root / "environment").read_text().splitlines()))
                first = fixture.pair(**env)
                self.assertEqual(0, first.returncode, first.stdout + first.stderr)
                build_log = pathlib.Path(str(fixture.output) + ".logs/build.stdout.log").read_text()
                receipts = [json.loads(line.removeprefix("LEAN_CACHE ")) for line in build_log.splitlines()
                            if line.startswith("LEAN_CACHE ")]
                self.assertEqual(1, len(receipts), build_log)
                self.assertEqual("not_attempted" if seed == "actions" else "unpacked" if seed == "release" else "miss",
                                 receipts[0]["archive_status"])
                if seed == "actions":
                    self.assertFalse((root / "gh-calls").exists())
                self.assertEqual(0, fixture.report_input("verify").returncode)
                second = fixture.pair(**env)
                self.assertEqual(0, second.returncode, second.stdout + second.stderr)
                self.assertIn("mode=reuse changed=0 added=0 removed=0 recheck=0", second.stdout)
                self.assertEqual(2, (root / "lake-runs").read_text().splitlines().count("build"))
                before = fixture.output.read_bytes()
                failed = fixture.pair(**dict(env, LAKE_BUILD_FAIL="19"))
                self.assertNotEqual(0, failed.returncode, failed.stdout + failed.stderr)
                self.assertEqual(before, fixture.output.read_bytes())


class AnalysisCacheTests(unittest.TestCase):
    def setUp(self):
        self.transport = lean_seed_contract.TransportTests("test_optional_fetch_valid_seed_still_reaches_build")
        self.transport.setUp()
        self.addCleanup(self.transport.doCleanups)
        self.root = self.transport.root
        self.bin = self.transport.bin
        self.cli = pathlib.Path(os.environ["ANALYSIS_TEST_CLI"])
        self.assertTrue(self.cli.is_file(), str(self.cli))
        self.dotnet = shutil.which("dotnet")
        self.assertIsNotNone(self.dotnet)
        self.runner = self.root / "tools/lean-inspector/LeanInformationAuditAnalysis/run-analysis-fixtures.sh"
        self.runner.parent.mkdir(parents=True)
        shutil.copy2(ROOT / self.runner.relative_to(self.root), self.runner)
        for name in ("CausalProjection", "FrozenRootAnalysis", "BoundedClosure"):
            write(self.runner.with_name(name + ".lean"), "-- private analysis input\n")
        for name in ("lean-cache-ensure.sh", "lean-cache-publish.sh", "lean_cache_release.py", "lean_cache.py"):
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

    def run_analysis(self, **extra):
        environment = self.transport.transport_environment(
            ANALYSIS_REAL_DOTNET=self.dotnet, ANALYSIS_TEST_CLI=str(self.cli),
            STRATALINT_LEAN_CLI_DLL=str(self.root.resolve() / "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"),
            LAKE_BIN=str(self.bin / "lake"), PYTHONPATH=str(self.bin),
            STRATALINT_LEAN_CACHE_DONORS="", XDG_CACHE_HOME=str(self.root / "cache"),
            STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS="300", **extra)
        result = subprocess.run(["bash", "-euo", "pipefail", "-c", '''
mkdir -p "$1/output"
"$2" "$1/output/artifacts" 2>&1 | tee "$1/output/run.log"
''', "analysis-caller", str(self.root), str(self.runner)], cwd=self.root,
            text=True, capture_output=True, env=environment)
        print(result.stdout, end="")
        print(result.stderr, end="")
        return result

    def assert_produced(self, result, archive_status):
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        receipts = [json.loads(line.removeprefix("LEAN_CACHE "))
                    for line in result.stdout.splitlines() if line.startswith("LEAN_CACHE ")]
        self.assertEqual(1, len(receipts), result.stdout)
        self.assertEqual(archive_status, receipts[0]["archive_status"])
        self.assertEqual(["exe cache get", "build LeanInformationAuditAnalysis"],
                         (self.root / "lake-runs").read_text().splitlines())
        self.assertEqual(7, len(list(self.output.iterdir())))
        self.assertIn("ANALYSIS_FIXTURES_EXIT=0", result.stdout)

    def test_absent_seed_reaches_analysis(self):
        self.prepare()
        self.assert_produced(self.run_analysis(), "miss")

    def test_corrupt_seed_reaches_analysis(self):
        self.prepare("corrupt")
        result = self.run_analysis()
        self.assert_produced(result, "miss")
        self.assertIn("checksum or size mismatch", result.stdout)
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
        self.assertEqual(19, result.returncode, result.stdout + result.stderr)
        self.assertIn('"archive_status":"unpacked"', result.stdout)
        self.assertIn("ANALYSIS_FIXTURES_EXIT=19", result.stdout)
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


# Keep the real make recipe and shell entrypoint, mapping its built candidate DLL
# path to the same CLI compiled by this test project.
DOTNET_LAUNCHER = '''#!/usr/bin/env bash
set -euo pipefail
[[ "$#" -eq 3 && "$1" == "$PWD/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll" &&
   "$2" == worktree && "$3" == ensure-cache ]] || exit 86
if [[ -n "${ANALYSIS_DOTNET_EXIT:-}" ]]; then exit "$ANALYSIS_DOTNET_EXIT"; fi
exec "$ANALYSIS_REAL_DOTNET" "$ANALYSIS_TEST_CLI" worktree ensure-cache --path "$PWD"
'''

LAKE = '''#!/usr/bin/env python3
import os, pathlib, sys
root = pathlib.Path.cwd()
args = sys.argv[1:]
with (root / "lake-runs").open("a") as log: log.write(" ".join(args) + "\\n")
if args == ["exe", "cache", "get"]:
    (root / ".lake/packages").mkdir(parents=True, exist_ok=True)
    sys.exit(int(os.environ.get("ANALYSIS_DEPENDENCY_EXIT", "0")))
assert args == ["build", "LeanInformationAuditAnalysis"], args
failure = int(os.environ.get("ANALYSIS_BUILD_EXIT", "0"))
if failure: sys.exit(failure)
output = pathlib.Path(os.environ["IE_PROJECTION_OUTPUT_DIR"])
for name in ("causal-analysis.json", "causal-analysis.txt", "frozen-seal.json",
             "frozen-analysis.json", "frozen-analysis.txt", "bounded-analysis.json",
             "bounded-analysis.txt"):
    (output / name).write_text("analysis-produced\\n")
'''


if __name__ == "__main__":
    unittest.main(verbosity=2)
