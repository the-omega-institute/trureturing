using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class CiTransportTests
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

    [Fact]
    public void CurrentCliTransportRoundTripRetainsRegistrationAndRejectsInvalidBundles()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Prepare(fixture, current: false);
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        var runtime = Path.GetDirectoryName(CommonExecutionEvidence.RunnerPath)!;
        Directory.CreateDirectory(Path.Combine(root, runtime));
        var binaries = Directory.GetFiles(Path.Combine(repository, runtime)).Select(file =>
        {
            var relative = runtime + "/" + Path.GetFileName(file);
            File.Copy(file, Path.Combine(root, relative));
            return relative;
        }).ToArray();
        SealEngineering(root, CommonExecutionEvidence.Candidate(root), binaries, Steps(CommonExecutionEvidence.EngineeringSteps));
        Report(root);
        CheckEvidenceFixture.Seal(root, "current", CommonExecutionEvidence.ValidateBuild(root));
        CommonExecutionEvidence.SealCurrent(root, CommonExecutionEvidence.ValidateBuild(root), Steps(CommonExecutionEvidence.CurrentSteps));
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/current.tgz");
        var packed = Cli("pack", root, archive);
        Assert.True(packed.Exit == 0, packed.Text);
        Assert.Contains("status=packed", packed.Text);

        var target = Path.Combine(root, "build/destination");
        Git(root, "clone", "--quiet", "--no-hardlinks", root, target);
        var restored = Cli("restore", target, archive);
        Assert.True(restored.Exit == 0, restored.Text);
        Assert.Contains("status=verified", restored.Text);
        Assert.Equal(File.ReadAllBytes(Path.Combine(root, "Meta/ci-checks.json")),
            File.ReadAllBytes(Path.Combine(target, "Meta/ci-checks.json")));
        Assert.Contains(CommonExecutionEvidence.ValidateCurrent(target).Materials, material => material.Path == "Meta/ci-checks.json");
        Assert.Equal(File.GetUnixFileMode(Path.Combine(root, Log)), File.GetUnixFileMode(Path.Combine(target, Log)));

        foreach (var defect in new[] { "extra", "extra-meta", "escape", "absolute", "symlink", "hardlink", "mode", "hash", "candidate", "round", "missing-registration" })
        {
            var damaged = Path.Combine(root, "build/" + defect + ".tgz");
            using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
            using (var reader = new TarReader(input))
            using (var output = new GZipStream(File.Create(damaged), CompressionLevel.Fastest))
            using (var writer = new TarWriter(output))
            {
                while (reader.GetNextEntry(copyData: true) is { } entry)
                {
                    if (defect == "missing-registration" && entry.Name == "Meta/ci-checks.json") continue;
                    if (entry.Name == Log && defect == "mode") entry.Mode ^= UnixFileMode.UserExecute;
                    if (entry.Name == Log && defect == "hash")
                        entry = new PaxTarEntry(TarEntryType.RegularFile, entry.Name) { Mode = entry.Mode,
                            ModificationTime = entry.ModificationTime, DataStream = new MemoryStream("corrupt"u8.ToArray()) };
                    if (entry.Name == CommonExecutionEvidence.CurrentPath && defect is "candidate" or "round")
                    {
                        var record = CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.CurrentPath);
                        var node = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(Path.Combine(root, entry.Name)))!;
                        node[defect] = defect == "candidate" ? new string('a', 64) : record.Round + "-stale";
                        entry.DataStream = new MemoryStream(System.Text.Encoding.UTF8.GetBytes(node.ToJsonString()));
                    }
                    writer.WriteEntry(entry);
                }
                var extra = defect switch { "extra" => "build/ci/undeclared", "extra-meta" => "Meta/undeclared.json",
                    "escape" => "../escaped", "absolute" => "/escaped", "symlink" or "hardlink" => "build/ci/link", _ => null };
                if (extra is not null)
                {
                    var type = defect == "symlink" ? TarEntryType.SymbolicLink : defect == "hardlink" ? TarEntryType.HardLink : TarEntryType.RegularFile;
                    var entry = new PaxTarEntry(type, extra);
                    if (type == TarEntryType.RegularFile) entry.DataStream = new MemoryStream("extra"u8.ToArray());
                    else entry.LinkName = Log;
                    writer.WriteEntry(entry);
                }
            }
            var rejected = Cli("restore", target, damaged);
            Assert.True(rejected.Exit == 2, defect + ": " + rejected.Text);
            Assert.DoesNotContain("status=verified", rejected.Text);
            Assert.False(File.Exists(Path.Combine(target, "build/ci/undeclared")));
            var recovered = Cli("restore", target, archive);
            Assert.True(recovered.Exit == 0, recovered.Text);
        }
        foreach (var (wrongCommit, run, attempt) in new[] { (commit, "18", "2"), (commit, "17", "3"), (new string('a', 40), "17", "2") })
        {
            var rejected = Cli("verify", target, archive, wrongCommit, run, attempt);
            Assert.True(rejected.Exit == 2, rejected.Text);
        }

        (int Exit, string Text) Cli(string command, string destination, string bundle, string? candidate = null, string run = "17", string attempt = "2") =>
            SharedBuildContractTests.Process(destination, "python3", ["-B", Path.Combine(repository, "tools/scripts/workflow/ci.py"),
                command, "--repository", destination, "--stage", "current", "--commit", candidate ?? commit,
                "--run-id", run, "--run-attempt", attempt, "--archive", bundle], hangGuard: TestBudgets.WorkflowProcessHangGuard);
    }

    [Theory]
    [InlineData("build")]
    [InlineData("engineering")]
    [InlineData("current")]
    [InlineData("engineering-seed")]
    [InlineData("current-seed")]
    public void NativeTransportSharesRequiredPayloadsAndRestoresIndependentFiles(string stage)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var root = fixture.Root;
        Prepare(fixture, stage.StartsWith("current", StringComparison.Ordinal));
        var owner = stage.Replace("-seed", "", StringComparison.Ordinal);
        var original = CommonExecutionEvidence.Read<CommonStageRecord>(root, "build/ci/" + owner + ".json");
        var equal = original.Materials.GroupBy(material => material.Sha256)
            .First(group => group.Count() > 1).Take(2).ToArray();
        File.SetLastWriteTimeUtc(Path.Combine(root, equal[0].Path), new DateTime(2020, 1, 2, 3, 4, 5, DateTimeKind.Utc));
        File.SetLastWriteTimeUtc(Path.Combine(root, equal[1].Path), new DateTime(2021, 2, 3, 4, 5, 6, DateTimeKind.Utc));
        if (owner == "current")
            File.SetUnixFileMode(Path.Combine(root, CommonExecutionEvidence.ReportPath + ".input.attestation"),
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/alias.tgz");
        Assert.Equal(0, Run("transport-pack", root, stage, commit, "17", "2", archive));
        var manifest = CommonExecutionEvidence.Read<CiTransportRecord>(root, CiTransport.ManifestPath(stage));
        var entries = new Dictionary<string, (TarEntryType Type, string Link, UnixFileMode Mode, DateTimeOffset Modified, long Length)>(StringComparer.Ordinal);
        using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
        using (var reader = new TarReader(input))
            while (reader.GetNextEntry() is { } entry)
                entries.Add(entry.Name, (entry.EntryType, entry.LinkName, entry.Mode, entry.ModificationTime, entry.Length));
        var seed = stage.EndsWith("-seed", StringComparison.Ordinal);
        var groups = manifest.Materials.GroupBy(material => (material.Sha256, material.Mode)).ToArray();
        Assert.Contains(groups, group => group.Count() > 1);
        foreach (var group in groups)
        {
            var paths = group.Select(material => material.Path).Order(StringComparer.Ordinal).ToArray();
            var regular = paths.Where(path => entries[path].Type is TarEntryType.RegularFile or TarEntryType.V7RegularFile).ToArray();
            Assert.True(regular.Length == (seed ? paths.Length : 1),
                $"{stage}: expected {(seed ? paths.Length : 1)} regular payloads for {group.Key}, actual {regular.Length}");
            foreach (var path in paths)
            {
                Assert.Equal((UnixFileMode)group.Key.Mode, entries[path].Mode);
                Assert.Equal(new DateTimeOffset(File.GetLastWriteTimeUtc(Path.Combine(root, path))).ToUnixTimeSeconds(),
                    entries[path].Modified.ToUnixTimeSeconds());
                if (seed || path == regular[0]) continue;
                Assert.Equal(TarEntryType.HardLink, entries[path].Type);
                Assert.Equal(regular[0], entries[path].Link);
                Assert.Equal(0, entries[path].Length);
            }
        }
        Assert.Equal(TarEntryType.RegularFile, entries[CiTransport.ManifestPath(stage)].Type);
        if (seed) return; // Optional seed consumers retain the existing regular-file format.
        if (owner == "current") Assert.Contains(manifest.Materials.GroupBy(material => material.Sha256),
            group => group.Select(material => material.Mode).Distinct().Count() > 1);
        var target = Path.Combine(root, "build/destination");
        Git(root, "clone", "--quiet", "--no-hardlinks", root, target);
        if (stage == "engineering")
        {
            var buildArchive = Path.Combine(root, "build/shared.tgz");
            Assert.Equal(0, Run("transport-pack", root, "build", commit, "17", "2", buildArchive));
            var shared = Extract(target, buildArchive, "build");
            Assert.True(shared.Exit == 0, shared.Text);
        }
        var restored = Extract(target, archive, stage);
        Assert.True(restored.Exit == 0, restored.Text);
        Assert.Equal(0, Run("transport-verify", target, stage, commit, "17", "2"));
        foreach (var material in manifest.Materials)
        {
            var source = Path.Combine(root, material.Path);
            var destination = Path.Combine(target, material.Path);
            Assert.Equal(File.ReadAllBytes(source), File.ReadAllBytes(destination));
            Assert.Equal(File.GetUnixFileMode(source), File.GetUnixFileMode(destination));
            Assert.Equal(entries[material.Path].Modified.ToUnixTimeSeconds(),
                new DateTimeOffset(File.GetLastWriteTimeUtc(destination)).ToUnixTimeSeconds());
            if (equal.Any(original => original.Path == material.Path))
                Assert.Equal(File.GetLastWriteTimeUtc(source), File.GetLastWriteTimeUtc(destination));
            Assert.Null(new FileInfo(destination).LinkTarget);
        }
        var pair = groups.First(group => group.Count() > 1).Take(2).Select(material => Path.Combine(target, material.Path)).ToArray();
        var untouched = File.ReadAllBytes(pair[1]);
        File.WriteAllText(pair[0], "independent mutation\n");
        Assert.Equal(untouched, File.ReadAllBytes(pair[1]));
    }

    [Theory]
    [InlineData("valid")]
    [InlineData("missing")]
    [InlineData("escape")]
    [InlineData("absolute")]
    [InlineData("self")]
    [InlineData("chain")]
    [InlineData("directory")]
    [InlineData("symlink")]
    [InlineData("manifest-target")]
    [InlineData("manifest-alias")]
    [InlineData("hash-association")]
    [InlineData("mode-association")]
    [InlineData("header-mode")]
    [InlineData("target-content")]
    public void DeclaredArchiveAliasesAreValidatedBeforeAnyMaterialIsWritten(string defect)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var root = fixture.Root;
        Prepare(fixture, current: false);
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/original.tgz");
        Assert.Equal(0, Run("transport-pack", root, "build", commit, "17", "2", archive));
        var manifestPath = CiTransport.ManifestPath("build");
        var manifest = CommonExecutionEvidence.Read<CiTransportRecord>(root, manifestPath);
        var pair = manifest.Materials.GroupBy(material => (material.Sha256, material.Mode))
            .First(group => group.Count() > 1).OrderBy(material => material.Path, StringComparer.Ordinal).Take(2).ToArray();
        var first = pair[0].Path;
        var alias = pair[1].Path;
        if (defect is "hash-association" or "mode-association")
            manifest = manifest with { Materials = manifest.Materials.Select(material => material.Path != alias ? material
                : defect == "hash-association" ? material with { Sha256 = new string('0', 64) }
                : material with { Mode = material.Mode ^ (int)UnixFileMode.UserExecute }).ToArray() };
        CommonExecutionEvidence.Write(root, manifestPath, manifest);
        var crafted = Path.Combine(root, "build/crafted.tgz");
        using (var output = new GZipStream(File.Create(crafted), CompressionLevel.Fastest))
        using (var writer = new TarWriter(output))
            foreach (var path in manifest.Materials.Select(material => material.Path).Append(manifestPath))
            {
                var type = path == alias || path == first && defect == "chain" || path == manifestPath && defect == "manifest-alias"
                    ? TarEntryType.HardLink : path == first && defect == "directory" ? TarEntryType.Directory
                    : path == first && defect == "symlink" ? TarEntryType.SymbolicLink : TarEntryType.RegularFile;
                var entry = new PaxTarEntry(type, path) { Mode = File.GetUnixFileMode(Path.Combine(root, path)),
                    ModificationTime = File.GetLastWriteTimeUtc(Path.Combine(root, path)) };
                if (type is TarEntryType.HardLink or TarEntryType.SymbolicLink)
                    entry.LinkName = path != alias ? alias : defect switch { "missing" => "build/ci/absent",
                        "escape" => "../escaped", "absolute" => "/escaped", "self" => alias,
                        "manifest-target" => manifestPath, _ => first };
                else if (type == TarEntryType.RegularFile)
                    entry.DataStream = new MemoryStream(path == first && defect == "target-content" ? "corrupt target"u8.ToArray()
                        : File.ReadAllBytes(Path.Combine(root, path)));
                if (path == alias && defect == "header-mode") entry.Mode ^= UnixFileMode.UserExecute;
                writer.WriteEntry(entry);
            }
        var target = Path.Combine(root, "build/empty-destination");
        Directory.CreateDirectory(target);
        if (defect == "target-content") Git(root, "clone", "--quiet", "--no-hardlinks", root, target);
        var extracted = Extract(target, crafted, "build");
        if (defect is not ("valid" or "target-content"))
        {
            Assert.True(extracted.Exit != 0, defect + ": " + extracted.Text);
            Assert.Empty(Directory.GetFileSystemEntries(target));
            return;
        }
        Assert.True(extracted.Exit == 0, extracted.Text);
        if (defect == "target-content")
        {
            Assert.Equal(commit, Git(target, "rev-parse", "HEAD"));
            Assert.Equal(2, Run("transport-verify", target, "build", commit, "17", "2"));
            Assert.Contains("artifact integrity mismatch: " + first,
                Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateBuild(target)).Message, StringComparison.Ordinal);
            return;
        }
        foreach (var material in manifest.Materials)
            Assert.Equal(File.ReadAllBytes(Path.Combine(root, material.Path)), File.ReadAllBytes(Path.Combine(target, material.Path)));
        var original = File.ReadAllBytes(Path.Combine(target, first));
        File.WriteAllText(Path.Combine(target, alias), "independent alias\n");
        Assert.Equal(original, File.ReadAllBytes(Path.Combine(target, first)));
    }

    private static (int Exit, string Text) Extract(string root, string archive, string stage) =>
        SharedBuildContractTests.Process(root, "python3", ["-B", "-c",
            "import pathlib,sys; sys.path.insert(0,sys.argv[1]); import ci; ci.extract(pathlib.Path(sys.argv[2]),pathlib.Path(sys.argv[3]),sys.argv[4])",
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow"), root, archive, stage],
            hangGuard: TestBudgets.WorkflowProcessHangGuard);

    [Fact]
    public void CurrentSealRequiresTheIncrementalSeedCompanion()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Prepare(fixture, current: false);
        Report(fixture.Root);
        TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + ".seed.json"));
        Assert.ThrowsAny<IOException>(() => CommonExecutionEvidence.SealCurrent(fixture.Root, CommonExecutionEvidence.ValidateBuild(fixture.Root), Steps(CommonExecutionEvidence.CurrentSteps)));
    }

    [Theory]
    [InlineData("build")]
    [InlineData("engineering")]
    [InlineData("current")]
    public void CompleteNulListedBundleMovesAcrossRootsAndPreservesExecutableModes(string stage)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Prepare(fixture, stage == "current");
        var commit = Git(fixture.Root, "rev-parse", "HEAD");
        var archive = Path.Combine(fixture.Root, "build", "transfer.tgz");
        Assert.Equal(0, Run("transport-pack", fixture.Root, stage, commit, "17", "2", archive));
        var target = Path.Combine(fixture.Root, "build", "destination");
        Git(fixture.Root, "clone", "--quiet", "--no-hardlinks", fixture.Root, target);
        if (stage == "engineering")
        {
            var buildArchive = Path.Combine(fixture.Root, "build", "build.tgz");
            Assert.Equal(0, Run("transport-pack", fixture.Root, "build", commit, "17", "2", buildArchive));
            using var shared = new GZipStream(File.OpenRead(buildArchive), CompressionMode.Decompress);
            TarFile.ExtractToDirectory(shared, target, overwriteFiles: true);
        }
        using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
            TarFile.ExtractToDirectory(input, target, overwriteFiles: true);
        Assert.Equal(0, Run("transport-verify", target, stage, commit, "17", "2"));
        Assert.Equal(stage == "engineering", TemporaryFileSystem.File.Exists(Path.Combine(target, CommonExecutionEvidence.EngineeringPath)));
        Assert.Equal(stage == "engineering", TemporaryFileSystem.File.Exists(Path.Combine(target, CommonExecutionEvidence.TestsPath)));
        Assert.Equal(stage == "current", TemporaryFileSystem.File.Exists(Path.Combine(target, CommonExecutionEvidence.CurrentPath)));
        if (!OperatingSystem.IsWindows())
            Assert.NotEqual(0, (int)(File.GetUnixFileMode(Path.Combine(target, Log)) & UnixFileMode.UserExecute));
        if (stage == "current")
            foreach (var suffix in new[] { "", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".seed.json" })
                Assert.Equal(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + suffix)),
                    TemporaryFileSystem.File.ReadAllBytes(Path.Combine(target, CommonExecutionEvidence.ReportPath + suffix)));
        Assert.Equal(2, Run("transport-verify", target, stage, commit, "18", "2"));
        Assert.Equal(2, Run("transport-verify", target, stage, commit, "17", "3"));
        Assert.Equal(2, Run("transport-verify", target, stage, new string('a', 40), "17", "2"));
        TemporaryFileSystem.File.AppendAllText(Path.Combine(target, Log), "corrupt");
        Assert.Equal(2, Run("transport-verify", target, stage, commit, "17", "2"));
    }

    [Theory]
    [InlineData("candidate")]
    [InlineData("failed-evidence")]
    [InlineData("missing-report")]
    [InlineData("missing-seed")]
    public void RequiredTransportCannotSealStaleOrIncompleteProduction(string defect)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Prepare(fixture, current: true);
        switch (defect)
        {
            case "candidate": TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, CurrentExecutionContractTests.CandidateFixture.First), "\n"); break;
            case "failed-evidence":
                var record = CommonExecutionEvidence.Read<CommonStageRecord>(fixture.Root, CommonExecutionEvidence.CurrentPath);
                CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.CurrentPath,
                    record with { Steps = record.Steps.Select(step => step with { Exit = 1 }).ToArray() });
                break;
            case "missing-report": TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath)); break;
            case "missing-seed": TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + ".seed.json")); break;
        }
        Assert.Equal(2, Run("transport-pack", fixture.Root, "current", Git(fixture.Root, "rev-parse", "HEAD"), "17", "2", Path.Combine(fixture.Root, "build", "bad.tgz")));
    }

    [Theory]
    [InlineData("valid")]
    [InlineData("undeclared")]
    [InlineData("corrupt")]
    public void TruthReleaseRestoresOnlyVerifiedCurrentArtifacts(string defect)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        PrepareCurrentRuntime(fixture);
        var root = fixture.Root;
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/current.tgz");
        Assert.Equal(0, Run("transport-pack", root, "current", commit, "17", "2", archive));
        var transfer = Path.Combine(root, "build/ci-current.tar.gz");
        using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
        using (var reader = new TarReader(input))
        using (var output = new GZipStream(File.Create(transfer), CompressionLevel.Fastest))
        using (var writer = new TarWriter(output))
        {
            while (reader.GetNextEntry(copyData: true) is { } entry)
            {
                if (defect == "corrupt" && entry.Name == Log)
                    entry = new PaxTarEntry(TarEntryType.RegularFile, entry.Name) { Mode = entry.Mode,
                        ModificationTime = entry.ModificationTime, DataStream = new MemoryStream("corrupt"u8.ToArray()) };
                writer.WriteEntry(entry);
            }
            if (defect == "undeclared")
                writer.WriteEntry(new PaxTarEntry(TarEntryType.RegularFile, "build/ci/undeclared")
                {
                    DataStream = new MemoryStream("extra"u8.ToArray()),
                });
        }
        var artifact = Path.Combine(root, "build/artifact.zip");
        using (var zip = ZipFile.Open(artifact, ZipArchiveMode.Create))
            zip.CreateEntryFromFile(transfer, "ci-current.tar.gz");
        var area = Path.Combine(root, "build/release");
        Directory.CreateDirectory(area);
        var result = SharedBuildContractTests.Process(root, "python3", ["-B", "-c", """
            import json, os, pathlib, shutil, subprocess, sys
            repository, root, area, artifact = map(pathlib.Path, sys.argv[1:5])
            commit, defect = sys.argv[5:]
            sys.path.insert(0, str(repository / 'tools/scripts/workflow'))
            import truth_release as owner
            repository_name = os.environ['GITHUB_REPOSITORY']
            workflow = dict(id=7, path='.github/workflows/ci-push.yml')
            run = dict(id=17, run_attempt=2, workflow_id=7, path=workflow['path'],
                       event='push', head_branch='dev', head_sha=commit, status='completed', conclusion='success')
            jobs = [dict(name=name, run_id=17, run_attempt=2, head_sha=commit,
                         status='completed', conclusion='success') for name in ('engineering', 'current')]
            responses = {
                'branches/dev': dict(protected=True),
                'actions/workflows/ci-push.yml': workflow,
                'commits?sha=dev&per_page=40': [dict(sha=commit)],
                'actions/workflows/ci-push.yml/runs?event=push&head_sha=' + commit + '&per_page=100':
                    [dict(workflow_runs=[run])],
                'actions/runs/17/attempts/2/jobs?per_page=100': [dict(jobs=jobs)],
                'actions/runs/17/artifacts?per_page=100': [dict(artifacts=[dict(id=170,
                    name='ci-current-17-2', expired=False, workflow_run=dict(id=17, head_sha=commit))])],
            }
            real_run = subprocess.run
            def github(command, **options):
                if command[0] != 'gh':
                    return real_run(command, **options)
                path = command[-1].removeprefix('repos/' + repository_name + '/')
                if path == 'actions/artifacts/170/zip':
                    with artifact.open('rb') as source:
                        shutil.copyfileobj(source, options['stdout'])
                    return subprocess.CompletedProcess(command, 0)
                return subprocess.CompletedProcess(command, 0, json.dumps(responses[path]))
            # Only GitHub is replaced. Selection, clone/checkout, extraction and
            # the transported native verifier all execute their production code.
            subprocess.run = github
            if defect == 'valid':
                selected = owner.select(root, area, owner.collect(repository_name, commit, workflow))
                candidate = owner.restore_candidate(root, area, selected)
                print('TRUTH_RELEASE_RESTORED ' + str(candidate))
            else:
                sys.argv = ['truth_release.py', 'prepare', '--repository', str(root), '--output', str(area)]
                raise SystemExit(owner.main())
            """, TestRepositoryLayout.FindRoot(), root, area, artifact, commit, defect],
            new Dictionary<string, string> {
                ["GITHUB_REPOSITORY"] = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "",
                ["CI_WORKFLOW_INPUTS"] = "null", ["GITHUB_OUTPUT"] = Path.Combine(area, "outputs") },
            hangGuard: TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        var target = Path.Combine(area, "candidate-17-2");
        if (defect == "valid")
        {
            Assert.Contains("run_id=17 run_attempt=2 status=verified", result.Text);
            Assert.Contains("TRUTH_RELEASE_RESTORED " + target, result.Text);
            var expected = CommonExecutionEvidence.ValidateCurrent(root);
            var restored = CommonExecutionEvidence.ValidateCurrent(target);
            Assert.Equal(expected.Candidate, restored.Candidate);
            Assert.Equal(expected.Round, restored.Round);
            Assert.Equal(expected.Materials, restored.Materials);
            Assert.Equal(File.ReadAllBytes(Path.Combine(root, "Meta/ci-checks.json")),
                File.ReadAllBytes(Path.Combine(target, "Meta/ci-checks.json")));
        }
        else
        {
            Assert.Contains(defect == "undeclared" ? "stage archive differs from declared transport materials"
                : "artifact integrity mismatch: " + Log, result.Text);
            Assert.Contains("TRUTH_RELEASE_INPUT_UNAVAILABLE", result.Text);
            Assert.Contains("publish_ready=false", File.ReadAllText(Path.Combine(area, "outputs")));
            Assert.DoesNotContain("status=verified", result.Text);
            Assert.False(File.Exists(Path.Combine(target, "build/ci/undeclared")));
            Assert.False(Directory.Exists(Path.Combine(area, "truth-release-assets")));
        }
    }


    private const string Log = "build/ci/fixture-executable";
    private static StageStep[] Steps(string[] names) => names.Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", Log)).ToArray();

    private static void PrepareCurrentRuntime(CurrentExecutionContractTests.CandidateFixture fixture)
    {
        Prepare(fixture, current: false);
        var root = fixture.Root;
        var runtime = Path.GetDirectoryName(CommonExecutionEvidence.RunnerPath)!;
        Directory.CreateDirectory(Path.Combine(root, runtime));
        var binaries = Directory.GetFiles(Path.Combine(TestRepositoryLayout.FindRoot(), runtime)).Select(file =>
        {
            var relative = runtime + "/" + Path.GetFileName(file);
            File.Copy(file, Path.Combine(root, relative));
            return relative;
        }).ToArray();
        SealEngineering(root, CommonExecutionEvidence.Candidate(root), binaries, Steps(CommonExecutionEvidence.EngineeringSteps));
        Report(root);
        CheckEvidenceFixture.Seal(root, "current", CommonExecutionEvidence.ValidateBuild(root));
        CommonExecutionEvidence.SealCurrent(root, CommonExecutionEvidence.ValidateBuild(root), Steps(CommonExecutionEvidence.CurrentSteps));
    }

    private static void Prepare(CurrentExecutionContractTests.CandidateFixture fixture, bool current)
    {
        fixture.Build();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) => { fixture.WriteTrx(results, "Passed"); return 0; }, TextWriter.Null));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, Log), "#!/bin/sh\nexit 0\n");
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Path.Combine(fixture.Root, Log), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var candidate = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath).Candidate;
        CiTransportTests.SealEngineering(fixture.Root, candidate, [Log], Steps(CommonExecutionEvidence.EngineeringSteps));
        if (!current) return;
        Report(fixture.Root);
        CheckEvidenceFixture.Seal(fixture.Root, "current", CommonExecutionEvidence.ValidateBuild(fixture.Root));
        CommonExecutionEvidence.SealCurrent(fixture.Root, CommonExecutionEvidence.ValidateBuild(fixture.Root), Steps(CommonExecutionEvidence.CurrentSteps));
    }

    internal static void SealEngineering(string root, string candidate, IEnumerable<string> binaries, StageStep[] steps)
    {
        var build = CommonExecutionEvidence.ValidateBuild(root);
        Assert.Equal(candidate, build.Candidate);
        build = build with { Materials = CommonExecutionEvidence.Materials(root,
            build.Materials.Select(material => material.Path).Concat(binaries)) };
        CommonExecutionEvidence.Write(root, CommonExecutionEvidence.BuildPath, build);
        var list = CommonExecutionEvidence.BundleListPath("build");
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root, list), string.Join('\0',
            build.Materials.Select(material => material.Path).Append(CommonExecutionEvidence.BuildPath).Append(list)
                .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)) + "\0");
        CheckEvidenceFixture.Seal(root, "engineering", build);
        CommonExecutionEvidence.SealEngineering(root, build, steps);
    }

    internal static (int Exit, string Text) ProduceReport(string root)
    {
        var repository = TestRepositoryLayout.FindRoot();
        return SharedBuildContractTests.Process(root, "python3", ["-B", "-c", """
            import pathlib, shutil, sys
            repository, root, relative = map(pathlib.Path, sys.argv[1:])
            sys.path.insert(0, str(repository / 'tools/tests/StrataLint.ScriptTests/Fixtures'))
            from report_snapshot_contract import SnapshotContracts
            case = SnapshotContracts()
            case.setUp()
            try:
                fixture = case.prepare_report()
                result = fixture.pair()
                print(result.stdout + result.stderr)
                assert result.returncode == 0
                sys.path.insert(0, str(repository / 'tools/lean-inspector'))
                from report_cache import copy_bundle, seed_valid
                from lean_cache import partition_path
                for name in ('D5', 'Trureturing.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
                    source, target = fixture.root / name, root / name
                    if source.is_dir(): shutil.copytree(source, target)
                    else: shutil.copyfile(source, target)
                copy_bundle(fixture.output, root / relative)
                assert seed_valid(root / relative, partition_path(root))
            finally:
                case.doCleanups()
            """, repository, root, CommonExecutionEvidence.ReportPath],
            hangGuard: TestBudgets.WorkflowProcessHangGuard);
    }

    internal static void Report(string root)
    {
        var report = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        TemporaryFileSystem.File.WriteAllText(report, "{\"modules\": [], \"schema\": \"stratalint-raw-lean-report-v2\"}\n");
        using (var stream = File.Create(report + ".materials.zip"))
        using (new ZipArchive(stream, ZipArchiveMode.Create)) { }
        foreach (var suffix in new[] { ".sha256", ".input.attestation", ".provenance.json", ".seed.json" })
            TemporaryFileSystem.File.WriteAllText(report + suffix, "fixture companion\n");
    }

    private static int Run(string command, string root, string stage, string commit, string run, string attempt, string? archive = null) =>
        Program.Run(new[] { command, "--repository", root, "--stage", stage, "--commit", commit, "--run-id", run, "--run-attempt", attempt }
            .Concat(archive is null ? [] : new[] { "--archive", archive }).ToArray(), TestResultEvidence.Load, TextWriter.Null, TextWriter.Null);

    private static string Git(string root, params string[] args)
    {
        var start = new ProcessStartInfo("git") { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var arg in args) start.ArgumentList.Add(arg);
        using var process = Process.Start(start)!;
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, error);
        return output.Trim();
    }
}
