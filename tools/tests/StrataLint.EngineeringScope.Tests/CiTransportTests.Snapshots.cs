using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CiTransportTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CurrentSnapshotAcceptanceUsesTheRemainingOptionalWorkerWindow(bool available)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ResourceRouteTests.ResourceFixture(["lean"]);
        var root = fixture.Root;
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\"}]}");
        var map = File.ReadAllText(Path.Combine(root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", string.Join('\n', map.Split('\n').Select(line =>
            line.Contains("id = \"lean\"", StringComparison.Ordinal)
                ? line.Replace("cache_layers = [], cache_activation = {}",
                    "cache_layers = [\"project\"], cache_activation = {project = \"lean-production\"}", StringComparison.Ordinal) : line)));
        fixture.CommitPlan();
        fixture.Write(".lake/build/new.olean", "new build output");
        fixture.Write("build/lean-cache/project/manifest.json", "previous accepted snapshot");
        var environment = new Dictionary<string, string> {
            ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev", ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "2",
            ["CANDIDATE_SHA"] = fixture.Commit, ["CI_PLAN_PATH"] = fixture.Plan, ["CI_CHANGES_PATH"] = fixture.Changes,
            ["CI_WORKFLOW_INPUTS"] = JsonSerializer.Serialize(new { candidate_sha = fixture.Commit }),
            ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "true",
            ["GITHUB_OUTPUT"] = Path.Combine(root, "build/cache-output") };
        var result = SharedBuildContractTests.Process(root, "python3", ["-B", "-c", """
            import os, pathlib, subprocess, sys, time
            repository, root = map(pathlib.Path, sys.argv[1:3])
            available = sys.argv[3] == 'true'
            sys.path.insert(0, str(repository / 'tools/scripts/worktree'))
            import cache_deadline, lean_actions
            marker = root / 'build/acceptance-entered'
            def outside(*args):
                raise AssertionError('optional acceptance ran outside the bounded snapshot worker')
            lean_actions.current_built_lean = outside
            cache_deadline.load_deadline = lambda *_: cache_deadline.CacheDeadline(
                time.monotonic() + (68 if available else 0))
            launch = subprocess.Popen
            child = '''
            import importlib.util, os, pathlib, signal, sys
            script = pathlib.Path(sys.argv[1])
            sys.path.insert(0, str(script.parent))
            spec = importlib.util.spec_from_file_location('lean_actions', script)
            owner = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(owner)
            def slow(root, *args):
                (root / 'build/acceptance-entered').write_text(str(os.getpid()))
                signal.pause()
            owner.current_built_lean = slow
            sys.argv = [str(script), *sys.argv[2:]]
            raise SystemExit(owner.main())
            '''
            import textwrap
            def start(command, **options):
                if '--snapshot-directory' in command:
                    command = [command[0], '-B', '-c', textwrap.dedent(child), *command[1:]]
                return launch(command, **options)
            lean_actions.subprocess.Popen = start
            sys.argv = ['lean_actions.py', 'snapshot', '--repository', str(root),
                '--stage', 'current', '--layer', 'project', '--bounded-cache']
            assert lean_actions.main() == 0
            assert marker.exists() == available
            if available:
                try: os.kill(int(marker.read_text()), 0)
                except ProcessLookupError: pass
                else: raise AssertionError('timed out acceptance worker remains alive')
            assert (root / 'build/lean-cache/project/manifest.json').read_text() == 'previous accepted snapshot'
            assert not list((root / 'build/lean-cache').glob('.snapshot-*'))
            """, TestRepositoryLayout.FindRoot(), root, available.ToString().ToLowerInvariant()], environment,
            TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("project_ready=false", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("project_ready=true", result.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void ReportBuildAndWarmReuseControlTheAcceptedCurrentProjectSnapshot()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ResourceRouteTests.ResourceFixture(["lean-report"]);
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        // Install the existing nonempty statement-producing runtime and shared
        // report entrypoints. Current and transport evidence are produced below.
        var installed = SharedBuildContractTests.Process(root, "python3", ["-B", "-c", """
            import pathlib, shutil, sys
            repository, root = map(pathlib.Path, sys.argv[1:])
            sys.path.insert(0, str(repository / 'tools/tests/StrataLint.ScriptTests/Fixtures'))
            from report_snapshot_contract import SnapshotContracts
            case = SnapshotContracts()
            case.setUp()
            try:
                source = case.prepare_report().root
                for name in ('D5', 'Trureturing.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                        'runtime', 'tools/scripts', 'tools/lean-inspector', 'tools/StrataLint.Lean',
                        'Meta/lean-report.toml', 'Meta/ReportProducers/lean-report.json'):
                    src, dst = source / name, root / name
                    if src.is_dir(): shutil.copytree(src, dst, dirs_exist_ok=True)
                    else:
                        dst.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copyfile(src, dst)
                runtime = root / 'runtime/bin/lean'
                needle = 'if args and args[0] == "build":\n    if os.environ.get("LAKE_EXPECT_NO_LAKE")'
                replacement = 'if args and args[0] == "build":\n    target = root / ".lake/build/lib/lean/D5/A.olean"\n    target.parent.mkdir(parents=True, exist_ok=True)\n    target.write_text("compiled fixture module")\n    if os.environ.get("LAKE_EXPECT_NO_LAKE")'
                text = runtime.read_text()
                assert text.count(needle) == 1
                runtime.write_text(text.replace(needle, replacement))
                shutil.copyfile(repository / 'Makefile', root / 'Makefile')
            finally:
                case.doCleanups()
            """, repository, root], hangGuard: TestBudgets.WorkflowProcessHangGuard);
        Assert.True(installed.Exit == 0, installed.Text);
        fixture.Write(".gitignore", File.ReadAllText(Path.Combine(root, ".gitignore")) + "lake-runs\n");
        var map = File.ReadAllText(Path.Combine(root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", string.Join('\n', map.Split('\n').Select(line =>
            line.Contains("id = \"lean-report\"", StringComparison.Ordinal)
                ? line.Replace("cache_layers = [], cache_activation = {}",
                    "cache_layers = [\"project\"], cache_activation = {project = \"lean-production\"}", StringComparison.Ordinal) : line)));
        fixture.Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Append(
            File.ReadAllText(Path.Combine(root, EngineeringRegistrationFixture.Path)),
            new EngineeringProjectFixture("tools/StrataLint.Lean/StrataLint.Lean.csproj", "StrataLint.Lean", "test-support", false,
                ["tools/StrataLint.Lean/Program.cs"]),
            new EngineeringProjectFixture("tools/scripts/report/JudgeSeedTask.csproj", "JudgeSeedTask", "test-support", false,
                ["tools/scripts/report/JudgeSeedTask.cs"])));
        fixture.CommitPlan();
        var compiled = SharedBuildContractTests.Process(root, "dotnet", ["build", "tools/StrataLint.Lean/StrataLint.Lean.csproj",
            "--configuration", "Release", "--nologo", "--verbosity", "quiet"], hangGuard: TestBudgets.WorkflowProcessHangGuard);
        Assert.True(compiled.Exit == 0, compiled.Text);
        var runtimeDirectory = Path.GetDirectoryName(CommonExecutionEvidence.RunnerPath)!;
        foreach (var file in Directory.GetFiles(Path.Combine(repository, runtimeDirectory), "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(root, runtimeDirectory, Path.GetRelativePath(Path.Combine(repository, runtimeDirectory), file));
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(file, target, true);
        }
        fixture.Write("build/ci/actual-helper-build.log", compiled.Text);
        CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root),
            [CommonExecutionEvidence.LeanProducerPath, CommonExecutionEvidence.RunnerPath],
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/actual-helper-build.log")).ToArray());
        var preparation = Path.Combine(root, "build/report-preparation");
        var snapshot = Path.Combine(root, "build/lean-cache/project/manifest.json");
        byte[]? savedSnapshot = null;
        foreach (var built in new[] { true, false })
        {
            if (Directory.Exists(preparation)) Directory.Delete(preparation, true);
            var runId = built ? "17" : "18";
            var environment = new Dictionary<string, string> {
                ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev", ["GITHUB_RUN_ID"] = runId, ["GITHUB_RUN_ATTEMPT"] = "2",
                ["GITHUB_REPOSITORY"] = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "",
                ["CANDIDATE_SHA"] = fixture.Commit, ["CI_PLAN_PATH"] = fixture.Plan, ["CI_CHANGES_PATH"] = fixture.Changes,
                ["CI_WORKFLOW_INPUTS"] = JsonSerializer.Serialize(new { candidate_sha = fixture.Commit }),
                ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "true",
                ["STRATALINT_LEAN_REPORT_PREPARATION"] = preparation, ["STRATALINT_REPORT_CACHE_ROOT"] = Path.Combine(root, "build/report-cache"),
                ["STRATALINT_SUPERVISOR_ROOT"] = Path.Combine(root, "build/supervisor"),
                ["LAKE_BIN"] = Path.Combine(root, "runtime/bin/lean"), ["LEAN_BIN"] = Path.Combine(root, "runtime/bin/lean"),
                ["GITHUB_OUTPUT"] = Path.Combine(root, "build/cache-output"), ["GITHUB_ENV"] = Path.Combine(root, "build/cache-environment") };
            var prepared = Call("python3", "-B", "tools/scripts/workflow/ci.py", "prepare-current", "--repository", root,
                "--commit", fixture.Commit, "--stage", "current", "--plan", fixture.Plan, "--changes", fixture.Changes);
            Assert.Contains("\"needs_lean_build\": " + built.ToString().ToLowerInvariant(), prepared, StringComparison.Ordinal);
            if (built) Assert.False(Directory.Exists(Path.Combine(root, ".lake")));
            Call("dotnet", CommonExecutionEvidence.RunnerPath, "current", "--repository", root, "--plan", fixture.Plan, "--changes", fixture.Changes);
            var current = CommonExecutionEvidence.ValidateCurrent(root);
            Assert.Equal("lean-report", Assert.Single(current.Steps).Name);
            using var result = JsonDocument.Parse(File.ReadAllText(Path.Combine(preparation, "result.json")));
            Assert.Equal(built, result.RootElement.GetProperty("lean_build_succeeded").GetBoolean());
            using var report = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, CommonExecutionEvidence.ReportPath)));
            var modules = report.RootElement.GetProperty("modules").EnumerateArray().ToArray();
            Assert.NotEmpty(modules);
            Assert.All(modules, module => Assert.NotEmpty(module.GetProperty("declarations").EnumerateArray()));
            Call("dotnet", CommonExecutionEvidence.RunnerPath, "transport-pack", "--repository", root, "--stage", "current",
                "--commit", fixture.Commit, "--run-id", runId, "--run-attempt", "2", "--archive", Path.Combine(root, "build/current.tgz"));
            var exported = Snapshot();
            Assert.Contains("project_ready=" + built.ToString().ToLowerInvariant(), exported, StringComparison.Ordinal);
            if (built) savedSnapshot = File.ReadAllBytes(snapshot);
            else Assert.Equal(savedSnapshot, File.ReadAllBytes(snapshot));
            if (built)
            {
                foreach (var defect in new[] { "run", "candidate", "current", "material" })
                {
                    var damaged = Path.Combine(root, defect switch {
                        "candidate" => "D5/A.lean", "current" => CommonExecutionEvidence.CurrentPath,
                        _ => CommonExecutionEvidence.ReportPath + ".materials.zip" });
                    var before = File.ReadAllBytes(damaged);
                    try
                    {
                        if (defect == "run") environment["GITHUB_RUN_ID"] = "19";
                        else File.AppendAllText(damaged, "changed accepted material");
                        Assert.Contains("project_ready=false", Snapshot(), StringComparison.Ordinal);
                        Assert.Equal(savedSnapshot, File.ReadAllBytes(snapshot));
                    }
                    finally
                    {
                        File.WriteAllBytes(damaged, before);
                        environment["GITHUB_RUN_ID"] = runId;
                    }
                }
            }
            Assert.Equal(1, File.ReadAllLines(Path.Combine(root, "lake-runs")).Count(line => line == "build"));
            Assert.Equal("", Git(root, "status", "--porcelain", "--untracked-files=all"));

            string Snapshot() => Call("python3", "-B", "-c", """
                import pathlib, sys
                root = pathlib.Path(sys.argv[1])
                sys.path.insert(0, str(root / 'tools/scripts/worktree'))
                import lean_actions
                run = lean_actions.subprocess.run
                def accepted_only(command, **options):
                    if command[0] == 'dotnet' and 'transport-verify' in command:
                        raise AssertionError('accepted current must not repeat native report semantic validation')
                    return run(command, **options)
                lean_actions.subprocess.run = accepted_only
                sys.argv = ['lean_actions.py', 'snapshot', '--repository', str(root), '--stage', 'current', '--layer', 'project']
                raise SystemExit(lean_actions.main())
                """, root);

            string Call(string executable, params string[] arguments)
            {
                var execution = SharedBuildContractTests.Process(root, executable, arguments, environment, TestBudgets.WorkflowProcessHangGuard);
                Assert.True(execution.Exit == 0, execution.Text);
                return execution.Text;
            }
        }
    }

    [Fact]
    public void ReportRestoreUsesTheExplicitCacheRootOutsideLake()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var result = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B", "-c", """
            import json, os, pathlib, sys
            root, repository = map(pathlib.Path, sys.argv[1:])
            sys.path.insert(0, str(repository / 'tools/scripts/worktree'))
            import lean_actions
            (root / 'lake-manifest.json').write_text(json.dumps({'packages':[{'name':'mathlib','rev':'a'*40}]}))
            cache = root / 'build/report-cache'
            os.environ.update(GITHUB_RUN_ID='17', GITHUB_RUN_ATTEMPT='2', STRATALINT_REPORT_CACHE_ROOT=str(cache))
            keys = lean_actions.actions_keys(root)
            assert pathlib.Path(keys['report']['target']) == cache.resolve(), keys['report']
            assert not (root / '.lake').exists()
            """, fixture.Root, TestRepositoryLayout.FindRoot()]);
        Assert.True(result.Exit == 0, result.Text);
    }

    [Theory]
    [InlineData("dependency")]
    [InlineData("project")]
    public void HeavySnapshotRequiresThisExecutionToHaveBuiltLean(string layer)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["current"]);
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\"}]}");
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", string.Join('\n', map.Split('\n').Select(line =>
            line.Contains("id = \"current\"", StringComparison.Ordinal)
                ? line.Replace("cache_layers = [], cache_activation = {}", "cache_layers = [\"" + layer
                    + "\"], cache_activation = {" + layer + " = \"lean-production\"}", StringComparison.Ordinal) : line)));
        fixture.CommitPlan();
        var source = Path.Combine(fixture.Root, layer == "dependency" ? ".lake/packages" : ".lake/build", "fixture.olean");
        Directory.CreateDirectory(Path.GetDirectoryName(source)!);
        File.WriteAllText(source, "existing optional seed");
        var environment = new Dictionary<string, string> {
            ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev", ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "2",
            ["CANDIDATE_SHA"] = fixture.Commit, ["CI_PLAN_PATH"] = fixture.Plan, ["CI_CHANGES_PATH"] = fixture.Changes,
            ["CI_WORKFLOW_INPUTS"] = JsonSerializer.Serialize(new { candidate_sha = fixture.Commit }),
            ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "true", ["STRATALINT_LEAN_REPORT_PREPARATION"] = "",
            ["GITHUB_OUTPUT"] = Path.Combine(fixture.Root, "build/cache-output") };
        var result = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B",
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py"), "snapshot",
            "--repository", fixture.Root, "--stage", "current", "--layer", layer], environment);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains(layer + "_ready=false", result.Text, StringComparison.Ordinal);
        Assert.Contains("this execution's Lean build result", result.Text, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, "build/lean-cache", layer)));
        Assert.Equal("existing optional seed", File.ReadAllText(source));
    }

    [Theory]
    [InlineData("valid", true)]
    [InlineData("run", false)]
    [InlineData("current", false)]
    public void StandaloneLeanSnapshotConsumesTheAcceptedCurrentExecution(string defect, bool ready)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["lean"]);
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\"}]}");
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", string.Join('\n', map.Split('\n').Select(line =>
            line.Contains("id = \"lean\"", StringComparison.Ordinal)
                ? line.Replace("cache_layers = [], cache_activation = {}",
                    "cache_layers = [\"project\"], cache_activation = {project = \"lean-production\"}", StringComparison.Ordinal) : line)));
        fixture.CommitPlan();
        fixture.Processes(prepareReport: false);
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        Assert.Equal("lean", Assert.Single(CommonExecutionEvidence.ValidateCurrent(fixture.Root).Steps).Name);
        var runtime = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/StrataLint.EngineeringScope/bin/Release/net10.0");
        foreach (var file in Directory.GetFiles(runtime, "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(fixture.Root, "tools/StrataLint.EngineeringScope/bin/Release/net10.0", Path.GetRelativePath(runtime, file));
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(file, target, true);
        }
        Assert.Equal(0, Run("transport-pack", fixture.Root, "current", fixture.Commit, "17", "2", Path.Combine(fixture.Root, "build/current.tgz")));
        var source = Path.Combine(fixture.Root, ".lake/build/fixture.olean");
        Directory.CreateDirectory(Path.GetDirectoryName(source)!);
        File.WriteAllText(source, "standalone build result");
        if (defect == "current") File.AppendAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath), "corruption");
        var environment = new Dictionary<string, string> {
            ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev", ["GITHUB_RUN_ID"] = defect == "run" ? "18" : "17", ["GITHUB_RUN_ATTEMPT"] = "2",
            ["CANDIDATE_SHA"] = fixture.Commit, ["CI_PLAN_PATH"] = fixture.Plan, ["CI_CHANGES_PATH"] = fixture.Changes,
            ["CI_WORKFLOW_INPUTS"] = JsonSerializer.Serialize(new { candidate_sha = fixture.Commit }),
            ["GITHUB_REPOSITORY"] = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "",
            ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "true", ["STRATALINT_LEAN_REPORT_PREPARATION"] = "",
            ["GITHUB_OUTPUT"] = Path.Combine(fixture.Root, "build/cache-output") };
        var result = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B",
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py"), "snapshot",
            "--repository", fixture.Root, "--stage", "current", "--layer", "project"], environment);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("project_ready=" + ready.ToString().ToLowerInvariant(), result.Text, StringComparison.Ordinal);
        Assert.Equal(ready, Directory.Exists(Path.Combine(fixture.Root, "build/lean-cache/project")));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath)));
    }

    [Fact]
    public void CurrentTransportFeedsOnlyTheDeclaredReportSnapshot()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        var evidence = Environment.GetEnvironmentVariable("CI_REPORT_SNAPSHOT_EVIDENCE");
        // Reuse the nonempty synthetic statement producer, not its manually
        // authored current/transport records. C# owns the actual handoff below.
        var inputs = ProduceReport(root);
        Capture("inputs.log", inputs.Text);
        Assert.True(inputs.Exit == 0, inputs.Text);
        Git(root, "add", "D5", "Trureturing.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain");
        Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "report inputs");
        Prepare(fixture, current: false);
        var build = CommonExecutionEvidence.ValidateBuild(root);
        CheckEvidenceFixture.Seal(root, "current", build);
        CommonExecutionEvidence.SealCurrent(root, build, Steps(CommonExecutionEvidence.CurrentSteps));
        CommonExecutionEvidence.Write(root, "build/ci/current-result.json", new Dictionary<string, object> {
            ["stage"] = "current", ["exit"] = 0, ["candidate"] = build.Candidate,
            ["current_evidence"] = CommonExecutionEvidence.CurrentPath, ["report"] = CommonExecutionEvidence.ReportPath });
        var commit = Git(root, "rev-parse", "HEAD");
        Assert.Equal(0, Run("transport-pack", root, "current", commit, "17", "2", Path.Combine(root, "build/current.tgz")));
        var transportPath = Path.Combine(root, "build/ci/current-transport.json");
        Assert.True(File.Exists(transportPath));
        Assert.False(File.Exists(Path.Combine(root, "build/ci/transport.json")));
        var transportBytes = File.ReadAllBytes(transportPath);
        var currentBytes = File.ReadAllBytes(Path.Combine(root, CommonExecutionEvidence.CurrentPath));
        var summaryBytes = File.ReadAllBytes(Path.Combine(root, "build/ci/current-result.json"));
        foreach (var name in new[] { "current-transport.json", "current.json", "current-result.json", "current-paths.nul", "build.json" })
            Capture(name, File.ReadAllText(Path.Combine(root, "build/ci", name)));
        var report = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        using var seed = JsonDocument.Parse(TemporaryFileSystem.File.ReadAllBytes(report + ".seed.json"));
        var partition = seed.RootElement.GetProperty("partition").GetString()!;
        var identity = Convert.ToHexStringLower(SHA256.HashData(TemporaryFileSystem.File.ReadAllBytes(report + ".seed.json")
            .Concat(TemporaryFileSystem.File.ReadAllBytes(report + ".provenance.json")).ToArray()));
        var suffixes = new[] { "", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".seed.json" };
        if (!string.IsNullOrEmpty(evidence))
            foreach (var suffix in suffixes) File.Copy(report + suffix, Path.Combine(evidence, "producer-report.json" + suffix));
        // Complete historical and foreign bundles exist locally but must not
        // be used to choose or populate this execution's remote snapshot.
        foreach (var history in new[] { partition + "/" + new string('0', 64), new string('b', 40) + "/foreign/old" })
            foreach (var suffix in suffixes)
            {
                var target = Path.Combine(root, ".lake/report-cache", history, "raw-lean-report.json" + suffix);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(report + suffix, target);
            }
        var environment = new Dictionary<string, string> {
            ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev",
            ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "2", ["CANDIDATE_SHA"] = commit,
            ["GITHUB_REPOSITORY"] = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "",
            ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "true",
            ["GITHUB_OUTPUT"] = Path.Combine(root, "build/snapshot-output") };
        Snapshot("accepted", ready: true);
        var cached = Path.Combine(root, "build/lean-cache/report");
        var manifestBytes = File.ReadAllBytes(Path.Combine(cached, "manifest.json"));
        Capture("snapshot-manifest.json", System.Text.Encoding.UTF8.GetString(manifestBytes));
        using var manifest = JsonDocument.Parse(manifestBytes);
        Assert.Equal("lean-actions-seed-v1", manifest.RootElement.GetProperty("schema").GetString());
        Assert.Equal("report", manifest.RootElement.GetProperty("layer").GetString());
        Assert.Equal(partition, manifest.RootElement.GetProperty("partition").GetString());
        var expected = suffixes.Select(suffix => (Path: partition + "/" + identity + "/raw-lean-report.json" + suffix,
            Sha: Convert.ToHexStringLower(SHA256.HashData(TemporaryFileSystem.File.ReadAllBytes(report + suffix))),
            Mode: OperatingSystem.IsWindows() ? 0 : (int)File.GetUnixFileMode(report + suffix)))
            .OrderBy(item => item.Path, StringComparer.Ordinal).ToArray();
        var actual = manifest.RootElement.GetProperty("files").EnumerateArray().Select(item => (
            Path: item.GetProperty("path").GetString()!, Sha: item.GetProperty("sha256").GetString()!, Mode: item.GetProperty("mode").GetInt32())).ToArray();
        Assert.Equal(expected, actual);
        Assert.Equal(expected.Select(item => item.Path), Directory.GetFiles(Path.Combine(cached, "data"), "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(Path.Combine(cached, "data"), path)).Order(StringComparer.Ordinal));
        foreach (var item in expected)
        {
            var path = Path.Combine(cached, "data", item.Path);
            Assert.Equal(item.Sha, Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path))));
            Assert.Equal(item.Mode, (int)File.GetUnixFileMode(path));
            if (!string.IsNullOrEmpty(evidence))
            {
                var copy = Path.Combine(evidence, "snapshot", item.Path);
                Directory.CreateDirectory(Path.GetDirectoryName(copy)!);
                File.Copy(path, copy);
                File.SetUnixFileMode(copy, File.GetUnixFileMode(path));
            }
        }
        var saved = Directory.GetFiles(cached, "*", SearchOption.AllDirectories).ToDictionary(path => path, File.ReadAllBytes);
        foreach (var defect in new[] { "missing-manifest", "wrong-run", "wrong-commit" })
        {
            if (defect == "missing-manifest") File.Delete(transportPath);
            if (defect == "wrong-run") environment["GITHUB_RUN_ID"] = "18";
            if (defect == "wrong-commit") environment["CANDIDATE_SHA"] = new string('0', 40);
            Snapshot(defect, ready: false);
            Assert.Equal(saved.Keys.Order(StringComparer.Ordinal), Directory.GetFiles(cached, "*", SearchOption.AllDirectories).Order(StringComparer.Ordinal));
            foreach (var item in saved) Assert.Equal(item.Value, TemporaryFileSystem.File.ReadAllBytes(item.Key));
            foreach (var item in expected) Assert.Equal(item.Mode, (int)File.GetUnixFileMode(Path.Combine(cached, "data", item.Path)));
            Assert.Equal(currentBytes, File.ReadAllBytes(Path.Combine(root, CommonExecutionEvidence.CurrentPath)));
            Assert.Equal(summaryBytes, File.ReadAllBytes(Path.Combine(root, "build/ci/current-result.json")));
            CommonExecutionEvidence.ValidateCurrent(root);
            File.WriteAllBytes(transportPath, transportBytes);
            environment["GITHUB_RUN_ID"] = "17";
            environment["CANDIDATE_SHA"] = commit;
        }

        // Bind each malformed current record into the transport so these cases
        // exercise the consumer contract beyond the outer file hash check.
        foreach (var defect in new[] { "version-one", "version-three", "candidate", "round", "missing-step", "missing-report-step", "reused-report" })
        {
            var current = CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.CurrentPath);
            var changed = defect switch
            {
                "version-one" => current with { Version = 1 },
                "version-three" => current with { Version = 3 },
                "candidate" => current with { Candidate = new string('a', 64) },
                "missing-step" => current with { Steps = current.Steps.Where(step => step.Name != "filemap").ToArray() },
                "missing-report-step" => current with { Steps = current.Steps.Where(step => step.Name != "lean-report").ToArray() },
                "reused-report" => current with { Steps = current.Steps.Select(step => step.Name == "lean-report" ? step with { Status = "reused" } : step).ToArray() },
                _ => current with { Round = current.Round + "-stale" },
            };
            CommonExecutionEvidence.Write(root, CommonExecutionEvidence.CurrentPath, changed);
            var transport = CommonExecutionEvidence.Read<CiTransportRecord>(root, "build/ci/current-transport.json");
            CommonExecutionEvidence.Write(root, "build/ci/current-transport.json", transport with
            {
                Materials = transport.Materials.Select(material => material.Path == CommonExecutionEvidence.CurrentPath
                    ? material with { Sha256 = CommonExecutionEvidence.Hash(Path.Combine(root, material.Path)) } : material).ToArray(),
            });
            Snapshot(defect, ready: false);
            foreach (var item in saved) Assert.Equal(item.Value, File.ReadAllBytes(item.Key));
            File.WriteAllBytes(Path.Combine(root, CommonExecutionEvidence.CurrentPath), currentBytes);
            File.WriteAllBytes(transportPath, transportBytes);
            CommonExecutionEvidence.ValidateCurrent(root);
        }

        void Snapshot(string label, bool ready)
        {
            File.Delete(environment["GITHUB_OUTPUT"]);
            var result = SharedBuildContractTests.Process(root, "python3", ["-B", Path.Combine(repository, "tools/scripts/worktree/lean_actions.py"),
                "snapshot", "--repository", root], environment);
            Capture(label + ".log", result.Text);
            Assert.True(result.Exit == 0, result.Text);
            Assert.True(TemporaryFileSystem.File.ReadAllText(environment["GITHUB_OUTPUT"]).Contains("report_ready=" + (ready ? "true" : "false"), StringComparison.Ordinal), result.Text);
            Assert.Contains(ready ? "\"status\": \"snapshot\"" : "\"status\": \"save-failed\"", result.Text, StringComparison.Ordinal);
            Assert.False(File.Exists(Path.Combine(root, "build/ci/transport.json")));
            Assert.Empty(Directory.GetDirectories(Path.Combine(root, "build/lean-cache"), ".snapshot-*"));
        }

        void Capture(string name, string text)
        {
            if (string.IsNullOrEmpty(evidence)) return;
            Directory.CreateDirectory(evidence);
            File.WriteAllText(Path.Combine(evidence, name), text);
        }
    }
}
