"""Small real SDK builds; Csc execution, runtime bytes and failures are the oracle."""
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path[:0] = [str(ROOT / "tools/scripts/report"), str(ROOT / "tools/scripts/worktree")]
import dotnet_producer as judge
import lean_actions as actions
from lean_cache import actions_keys
from unittest import mock


class CompilerSeeds(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="judge-seed-")
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name).resolve()
        self.env = dict(os.environ, CI="true", DOTNET_CLI_UI_LANGUAGE="en-US",
                        GITHUB_RUN_ID="17", GITHUB_RUN_ATTEMPT="2", GITHUB_EVENT_NAME="push",
                        GITHUB_REF="refs/heads/dev", STRATALINT_CACHE_WRITES="true",
                        STRATALINT_CHECK_SUCCEEDED="false", STRATALINT_BUILD_SUCCEEDED="true")
        self.env.pop("CustomAfterMicrosoftCSharpTargets", None)
        self.observations = []
        self.write("lake-manifest.json", json.dumps({"packages": [{"name": "mathlib", "rev": "a" * 40}]}))
        self.write("Directory.Build.props", '<Project><PropertyGroup><TargetFramework>net10.0</TargetFramework>'
                   '<RestorePackagesWithLockFile>true</RestorePackagesWithLockFile><Deterministic>true</Deterministic>'
                   '</PropertyGroup></Project>')
        self.write("tools/Library/Library.csproj", '<Project Sdk="Microsoft.NET.Sdk"><ItemGroup>'
                   '<EmbeddedResource Include="message.txt" LogicalName="message"/>'
                   '<AdditionalFiles Include="generator-input.txt"/></ItemGroup></Project>')
        self.write("tools/Library/Code.cs", 'public static class Library { public static int Value() => 1; }')
        self.write("tools/Library/message.txt", "first resource")
        self.write("tools/Library/generator-input.txt", "first additional input")
        self.write("tools/Consumer/Consumer.csproj", '<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup>'
                   '<OutputType>Exe</OutputType></PropertyGroup><ItemGroup>'
                   '<ProjectReference Include="../Library/Library.csproj"/>'
                   '<None Update="data.sh" CopyToOutputDirectory="PreserveNewest"/>'
                   '</ItemGroup></Project>')
        self.write("tools/Consumer/Program.cs", 'System.Console.WriteLine(Library.Value());')
        self.write("tools/Consumer/data.sh", 'echo first\n')
        self.run_dotnet("new", "sln", "--format", "sln", "--name", "StrataLint", "--output", "tools")
        self.run_dotnet("sln", "tools/StrataLint.sln", "add", "tools/Library/Library.csproj", "tools/Consumer/Consumer.csproj")
        self.run_dotnet("restore", "tools/StrataLint.sln", "--use-lock-file")

    def tearDown(self):
        evidence = os.environ.get("JUDGE_SEED_EVIDENCE")
        if evidence:
            directory = pathlib.Path(evidence)
            directory.mkdir(parents=True, exist_ok=True)
            (directory / (self._testMethodName + ".json")).write_text(json.dumps(self.observations, indent=2) + "\n")

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def run_dotnet(self, *arguments, success=True):
        result = subprocess.run(["dotnet", *arguments], cwd=self.root, env=self.env, text=True, capture_output=True)
        if success:
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        return result

    def prepare(self):
        with mock.patch.dict(os.environ, self.env):
            target = judge.prepare_seed(self.root)
        self.env["CustomAfterMicrosoftCSharpTargets"] = str(target)

    def build(self, name, *, expected=None, properties=(), success=True, project="tools/StrataLint.sln"):
        self.run_dotnet("restore", project, "--locked-mode")
        result = self.run_dotnet("build", project, "--no-restore", "--configuration", "Release",
                                 "--warnaserror", "-v:diag", *properties, success=success)
        csc = len(re.findall(r'Task "Csc"(?: \(TaskId:\d+\))?', result.stdout))
        self.observations.append({"name": name, "exit": result.returncode, "csc_tasks": csc})
        evidence = os.environ.get("JUDGE_SEED_EVIDENCE")
        if evidence:
            pathlib.Path(evidence).mkdir(parents=True, exist_ok=True)
            (pathlib.Path(evidence) / (self._testMethodName + "-" + name + ".log")).write_text(result.stdout + result.stderr)
        if expected is not None:
            self.assertEqual(expected, csc, result.stdout[-12000:] + result.stderr)
        return result

    def dll(self, project, name=None):
        return self.root / f"tools/{project}/bin/Release/net10.0/{name or project}.dll"

    def products(self):
        return {str(path.relative_to(self.root)): hashlib.sha256(path.read_bytes()).hexdigest()
                for project in ("Library", "Consumer") for path in self.dll(project).parent.iterdir() if path.is_file()}

    def checkout_times(self):
        stamp = max(path.stat().st_mtime_ns for path in self.root.rglob("*.dll")) + 1000
        for path in self.root.rglob("*"):
            if path.is_file() and path.suffix in (".cs", ".csproj", ".props", ".sh") and not {"bin", "obj", "build", ".judge-binaries"}.intersection(path.relative_to(self.root).parts):
                os.utime(path, ns=(stamp, stamp))

    def snapshot(self):
        self.assertFalse((self.root / "build/ci/current-transport.json").exists())
        self.assertFalse((self.root / "build/ci/current.json").exists())
        with mock.patch.dict(os.environ, self.env):
            keys = actions_keys(self.root)
        result = subprocess.run([sys.executable, "-B", str(ROOT / "tools/scripts/worktree/lean_actions.py"),
                                 "snapshot", "--repository", str(self.root), "--layers", "judge"],
                                env=self.env, text=True, capture_output=True)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn("judge_ready=true", result.stdout)
        self.assertNotIn("report_ready=", result.stdout)
        self.observations.append({"name": "judge-only-snapshot", "exit": result.returncode,
                                  "stdout": result.stdout, "current_handoff_present": False})
        self.assertTrue((self.root / keys["judge"]["path"] / "manifest.json").is_file())
        return keys

    def restore(self, keys):
        for project in ("Library", "Consumer"):
            for kind in ("bin", "obj"):
                shutil.rmtree(self.root / "tools" / project / kind, ignore_errors=True)
        actions.restore(self.root, keys, {"judge": keys["judge"]["key"]}, ("judge",))
        self.checkout_times()
        self.prepare()

    def test_helper_readme_commit_and_source_change(self):
        # The helper excludes root build properties, so exercise its production
        # project in a real Git repository, including its own Csc execution.
        inputs = ["global.json", "tools/scripts/report/JudgeSeedTask.csproj",
                  "tools/scripts/report/JudgeSeedTask.cs", "tools/scripts/report/packages.lock.json"]
        for path in inputs:
            self.write(path, (ROOT / path).read_text())
        self.write(".gitignore", "build/\n**/bin/\n**/obj/\n")
        self.write("README.md", "helper fixture\n")
        empty = self.root / "build/empty-git-config"
        empty.mkdir(parents=True)

        def git(*arguments):
            result = subprocess.run(["git", "-c", "core.hooksPath=" + str(empty), "-c", "commit.gpgsign=false",
                                     "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", *arguments],
                                    cwd=self.root, env=self.env, text=True, capture_output=True)
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            return result.stdout.strip()

        git("init", "--quiet", "--template=" + str(empty))
        git("add", ".")
        git("commit", "--quiet", "-m", "helper compiler inputs")
        before = git("rev-parse", "HEAD", "HEAD^{tree}").splitlines()
        hashes = {path: hashlib.sha256((self.root / path).read_bytes()).hexdigest() for path in inputs}
        project = "tools/scripts/report/JudgeSeedTask.csproj"
        self.build("helper-cold", project=project, expected=1)
        dll = self.dll("scripts/report", "JudgeSeedTask")
        original = dll.read_bytes()
        self.write("README.md", "helper fixture with updated documentation\n")
        git("add", "README.md")
        git("commit", "--quiet", "-m", "README only")
        after = git("rev-parse", "HEAD", "HEAD^{tree}").splitlines()
        self.assertTrue(all(first != second for first, second in zip(before, after)))
        self.assertEqual("README.md", git("diff", "--name-only", before[0], after[0]))
        self.assertEqual("", git("status", "--porcelain"))
        self.assertEqual(hashes, {path: hashlib.sha256((self.root / path).read_bytes()).hexdigest() for path in inputs})
        self.observations.append({"name": "helper-commits", "cold": before, "warm": after, "inputs": hashes})
        self.build("helper-readme", project=project, expected=0)
        self.assertEqual(original, dll.read_bytes())
        source = self.root / "tools/scripts/report/JudgeSeedTask.cs"
        source.write_text(source.read_text() + "\ninternal static class ChangedHelperSource { }\n")
        self.build("helper-source", project=project, expected=1)
        self.assertNotEqual(original, dll.read_bytes())

    def test_checkout_and_runtime_copy(self):
        self.prepare()
        self.build("cold", expected=2)
        original = self.dll("Consumer").read_bytes()
        for override in ({"GITHUB_EVENT_NAME": "pull_request_target"},
                         {"GITHUB_EVENT_NAME": "pull_request"},
                         {"GITHUB_EVENT_NAME": "workflow_dispatch"},
                         {"GITHUB_REF": "refs/heads/other"},
                         {"STRATALINT_CACHE_WRITES": "false"},
                         {"STRATALINT_BUILD_SUCCEEDED": "false", "STRATALINT_CHECK_SUCCEEDED": "true"},
                         {"STRATALINT_BUILD_SUCCEEDED": ""}):
            with self.subTest(writer=override), mock.patch.dict(os.environ, dict(self.env, **override)):
                keys = actions_keys(self.root)
                shutil.rmtree(self.root / keys["judge"]["path"], ignore_errors=True)
                actions.snapshot(self.root, keys, ("judge",))
                self.assertFalse((self.root / keys["judge"]["path"] / "manifest.json").exists())
        with mock.patch.dict(os.environ, self.env):
            self.assertFalse(actions_keys(self.root)["save_allowed"])
        keys = self.snapshot()
        self.restore(keys)
        self.build("new-checkout", expected=0)
        self.assertEqual(original, self.dll("Consumer").read_bytes())
        self.write("tools/Library/Code.cs", 'public static class Library { public static int Value() => 2; }')
        self.build("dependency-implementation", expected=1)
        self.assertEqual(original, self.dll("Consumer").read_bytes())
        self.assertEqual(self.dll("Library").read_bytes(), self.dll("Consumer", "Library").read_bytes())
        self.assertEqual("2", self.run_dotnet(str(self.dll("Consumer"))).stdout.strip())
        script = self.root / "tools/Consumer/data.sh"
        stamp = script.stat().st_mtime_ns
        script.write_text("echo changed\n")
        os.utime(script, ns=(stamp, stamp))
        self.build("copied-data", expected=0)
        self.assertEqual("echo changed\n", (self.dll("Consumer").parent / "data.sh").read_text())

    def test_semantics_membership_and_clean_equivalence(self):
        self.prepare()
        self.build("cold", expected=2)
        self.build("option", properties=("-p:Optimize=false",), expected=2)
        incremental = self.products()
        self.build("clean-option", properties=("-p:Optimize=false", "-t:Rebuild"), expected=2)
        self.assertEqual(incremental, self.products())
        self.write("tools/Library/Added.cs", "// added compiler input\n")
        self.build("membership", properties=("-p:Optimize=false",), expected=1)
        project = self.root / "tools/Library/Library.csproj"
        project.write_text(project.read_text().replace("</Project>", "<PropertyGroup><DefineConstants>CHANGED</DefineConstants></PropertyGroup></Project>"))
        self.build("project", properties=("-p:Optimize=false",), expected=1)
        (self.root / "tools/Library/Added.cs").unlink()
        self.build("removed-input", properties=("-p:Optimize=false",), expected=1)
        resource = self.root / "tools/Library/message.txt"
        stamp = resource.stat().st_mtime_ns
        resource.write_text("changed resource")
        os.utime(resource, ns=(stamp, stamp))
        self.build("preserved-time-resource", properties=("-p:Optimize=false",), expected=1)
        self.write("tools/Library/generator-input.txt", "changed additional input")
        self.build("additional-input", properties=("-p:Optimize=false",), expected=1)
        self.build("generated-assembly-info", properties=("-p:Optimize=false", "-p:Version=2.0.0"), expected=2)

    def test_corrupt_missing_material_and_relocation(self):
        self.prepare()
        self.build("cold", expected=2)
        keys = self.snapshot()
        cached = self.root / keys["judge"]["path"] / "data"
        victim = next(cached.rglob("Consumer.dll"))
        stamp = victim.stat().st_mtime_ns
        victim.write_bytes(b"corrupt")
        os.utime(victim, ns=(stamp, stamp))
        self.restore(keys)
        self.build("corrupt-transfer", expected=2)
        keys = self.snapshot()
        self.restore(keys)
        self.build("runtime-rematerialization", expected=0)
        original = self.dll("Consumer").read_bytes()
        self.dll("Consumer").unlink()
        self.build("missing-runtime", expected=0)
        victim = self.dll("Consumer")
        stamp = victim.stat().st_mtime_ns
        victim.write_bytes(b"corrupt")
        os.utime(victim, ns=(stamp, stamp))
        self.build("preserved-time-runtime-corruption", expected=0)
        self.assertEqual(original, self.dll("Consumer").read_bytes())
        victim = self.root / "tools/Consumer/obj/Release/net10.0/Consumer.dll"
        stamp = victim.stat().st_mtime_ns
        victim.write_bytes(b"corrupt")
        os.utime(victim, ns=(stamp, stamp))
        self.build("preserved-time-intermediate-corruption", expected=1)
        self.assertEqual(original, self.dll("Consumer").read_bytes())
        (victim.parent / "Consumer.pdb").unlink()
        self.build("missing-intermediate", expected=1)
        keys = self.snapshot()
        moved = tempfile.TemporaryDirectory(prefix="judge-relocated-")
        self.addCleanup(moved.cleanup)
        new_root = pathlib.Path(moved.name).resolve()
        shutil.copytree(self.root, new_root, dirs_exist_ok=True)
        self.root = new_root
        self.restore(keys)
        self.build("unsupported-relocation", expected=2)
        self.assertEqual("1", self.run_dotnet(str(self.dll("Consumer"))).stdout.strip())

    def test_no_seed_or_save_failure_cannot_pass_bad_compilation(self):
        self.prepare()
        self.write("tools/Library/Code.cs", "not valid C#")
        self.assertNotEqual(0, self.build("no-seed-bad-source", success=False).returncode)
        self.write("tools/Library/Code.cs", 'public static class Library { public static int Value() => 1; }')
        self.build("repair", expected=2)
        with mock.patch.dict(os.environ, self.env):
            keys = actions_keys(self.root)
            with mock.patch.object(actions.shutil, "copytree", side_effect=OSError("fixture save failure")) as copy:
                actions.snapshot(self.root, keys, ("judge",))
            self.assertGreater(copy.call_count, 0)
        self.assertFalse((self.root / keys["judge"]["path"] / "manifest.json").exists())
        self.write("tools/Library/Code.cs", "not valid C#")
        self.assertNotEqual(0, self.build("save-failed-bad-source", success=False).returncode)


if __name__ == "__main__":
    unittest.main()
