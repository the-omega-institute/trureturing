using System.Diagnostics;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class ExecutionSeedTransportBehaviorTests
{
    [Fact]
    public void IsolatedEngineeringArtifactsExportReusableSeedWithoutProducerOrBuildTools()
    {
        if (OperatingSystem.IsWindows()) throw Xunit.Sdk.SkipException.ForSkip("native tar transport fixture is unsupported on Windows");
        using var producer = Prepare("engineering", plannedEngineering: true);
        using var storage = new CurrentExecutionContractTests.CandidateFixture();
        var repository = TestRepositoryLayout.FindRoot();
        var commit = SharedBuildContractTests.Git(producer.Root, "rev-parse", "HEAD");
        var beforeCommit = SharedBuildContractTests.Git(producer.Root, "rev-parse", "HEAD^1");
        var runtime = Path.GetDirectoryName(CommonExecutionEvidence.RunnerPath)!;
        var original = CommonExecutionEvidence.ValidateEngineering(producer.Root);
        CiTransportTests.SealEngineering(producer.Root, original.Candidate,
            Directory.GetFiles(Path.Combine(producer.Root, runtime)).Select(path => runtime + "/" + Path.GetFileName(path)), original.Steps);
        var checks = CommonExecutionEvidence.Read<CommonCheckRecord>(producer.Root, CommonExecutionEvidence.ChecksPath("engineering"));
        var tests = CommonExecutionEvidence.Read<TestExecutionRecord>(producer.Root, CommonExecutionEvidence.TestsPath);
        var archives = new Dictionary<string, string>();
        foreach (var stage in new[] { "build", "engineering" })
        {
            var archive = Path.Combine(storage.Root, "build", stage + ".tgz");
            var packed = Workflow(producer.Root, "pack", stage, commit, archive, Environment(commit, producer.Root, "81", "1"));
            Assert.True(packed.Exit == 0, packed.Text);
            archives.Add(stage, archive);
        }
        var targets = new[] { "exporter", "consumer" }.Select(name => Path.Combine(storage.Root, "build", name)).ToArray();
        foreach (var target in targets)
        {
            SharedBuildContractTests.Git(producer.Root, "clone", "--quiet", "--no-hardlinks", producer.Root, target);
            Assert.False(Directory.Exists(Path.Combine(target, "build")));
            Assert.False(Directory.Exists(Path.Combine(target, runtime)));
            Assert.Equal("", SharedBuildContractTests.Git(target, "status", "--porcelain", "--untracked-files=all"));
        }
        // Only the two normal artifacts survive; no producer seed or output
        // directory can accidentally satisfy a missing transport dependency.
        Directory.Delete(producer.Root, recursive: true);
        Directory.CreateDirectory(producer.Root);
        var dotnet = SharedBuildContractTests.Process(storage.Root, "which", ["dotnet"]).Text.Trim();
        storage.Write("build/guard/dotnet", """
            #!/bin/sh
            set -eu
            printf '%s\n' "$*" >> "$CONTRACT_CALLS"
            case "$1" in *StrataLint.EngineeringScope.dll) ;; *) exit 91 ;; esac
            case "$2" in transport-pack|transport-verify) ;; *) exit 92 ;; esac
            exec "$CONTRACT_DOTNET" "$@"
            """);
        foreach (var command in new[] { "lake", "elan", "make", "msbuild" })
            storage.Write("build/guard/" + command, "#!/bin/sh\nprintf '%s\\n' forbidden >> \"$CONTRACT_CALLS\"\nexit 93\n");
        storage.Write("build/guard/gh", """
            #!/bin/sh
            set -eu
            test "$*" = 'api repos/fixture/repo/actions/runs/81/attempts/1/jobs?per_page=100'
            cat "$CONTRACT_JOBS"
            """);
        storage.Write("build/cache-jobs.json", JsonSerializer.Serialize(new { total_count = 1, jobs = new[] { new
        {
            id = 91, name = "engineering_cache", run_id = 81, run_attempt = 1, head_sha = commit,
            status = "in_progress", runner_name = "fixture-runner", started_at = "2026-01-01T00:00:00Z",
        } } }));
        foreach (var path in Directory.GetFiles(Path.Combine(storage.Root, "build/guard")))
            File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var calls = Path.Combine(storage.Root, "build/tool-calls");
        Dictionary<string, string> IsolatedEnvironment(string target, string run)
        {
            var environment = Environment(commit, target, run, "1");
            environment["PATH"] = Path.Combine(storage.Root, "build/guard") + Path.PathSeparator + System.Environment.GetEnvironmentVariable("PATH");
            environment["CONTRACT_DOTNET"] = dotnet;
            environment["CONTRACT_CALLS"] = calls;
            environment["CONTRACT_JOBS"] = Path.Combine(storage.Root, "build/cache-jobs.json");
            environment["NUGET_PACKAGES"] = Path.Combine(target, "build/absent-packages");
            environment["ELAN_HOME"] = Path.Combine(target, "build/absent-elan");
            environment["CI_PLAN_PATH"] = "build/ci/plan.json";
            environment["CI_CHANGES_PATH"] = "build/ci/changes.json";
            environment["CI_PUSH_BEFORE"] = "";
            environment["CI_PUSH_AFTER"] = "";
            environment["CI_NEEDS"] = "{\"build\":{\"result\":\"success\"},\"engineering\":{\"result\":\"success\"}}";
            environment["GITHUB_SHA"] = commit;
            environment["GITHUB_JOB"] = "engineering_cache";
            environment["RUNNER_NAME"] = "fixture-runner";
            environment["GITHUB_EVENT_PATH"] = Path.Combine(storage.Root, "build/push-event.json");
            return environment;
        }
        storage.Write("build/push-event.json", JsonSerializer.Serialize(new { before = beforeCommit, after = commit }));
        var exporter = targets[0];
        var exportEnvironment = IsolatedEnvironment(exporter, "81");
        var missingPlan = Python(exporter, repository, ["keys", "--repository", exporter, "--stage", "engineering"], exportEnvironment);
        Assert.True(missingPlan.Exit == 2, missingPlan.Text);
        Assert.Contains("changes.json", missingPlan.Text, StringComparison.Ordinal);
        var missingEvent = StageInput(exporter, commit, new(exportEnvironment) { ["GITHUB_EVENT_PATH"] = "" });
        Assert.True(missingEvent.Exit == 2, missingEvent.Text);
        Assert.Contains("native push requires the actual fixed event input", missingEvent.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(exporter, "build/ci/plan.json")));
        var planned = StageInput(exporter, commit, exportEnvironment);
        Assert.True(planned.Exit == 0, planned.Text);
        Assert.Contains("\"required\": true", planned.Text, StringComparison.Ordinal);
        var plan = JsonNode.Parse(File.ReadAllText(Path.Combine(exporter, exportEnvironment["CI_PLAN_PATH"])))!;
        Assert.Equal("push", plan["mode"]!.ToString());
        Assert.Null(plan["base"]);
        Assert.Null(plan["head"]);
        Assert.Equal(beforeCommit, plan["origin"]!["before"]!.ToString());
        Assert.Equal(commit, plan["origin"]!["after"]!.ToString());
        Assert.Equal("not-applicable", plan["stages"]!["delta"]!["status"]!.ToString());
        var changesPath = Path.Combine(exporter, exportEnvironment["CI_CHANGES_PATH"]);
        var completeChanges = File.ReadAllText(changesPath);
        var incomplete = JsonNode.Parse(completeChanges)!;
        Assert.NotEmpty(incomplete["changes"]!.AsArray());
        incomplete["changes"] = new JsonArray();
        incomplete["change_count"] = 0;
        File.WriteAllText(changesPath, incomplete.ToJsonString());
        var badRange = StageInput(exporter, commit, exportEnvironment);
        Assert.True(badRange.Exit == 2, badRange.Text);
        Assert.Contains("changed-path", badRange.Text, StringComparison.Ordinal);
        var badKeys = Python(exporter, repository, ["keys", "--repository", exporter, "--stage", "engineering"], exportEnvironment);
        Assert.True(badKeys.Exit == 2, badKeys.Text);
        string[] snapshotArguments = ["snapshot", "--repository", exporter, "--stage", "engineering", "--layer", "engineering", "--bounded-cache"];
        var badSnapshot = CacheWithFixedClock(exporter, repository, "lean_actions", snapshotArguments, exportEnvironment);
        Assert.True(badSnapshot.Exit == 2, badSnapshot.Text);
        Assert.DoesNotContain("engineering_ready=true", badSnapshot.Text, StringComparison.Ordinal);
        File.WriteAllText(changesPath, completeChanges);
        // The rejected invocations end their jobs. Reset their local failure
        // receipt before exercising the independent successful job below.
        File.Delete(Path.Combine(exporter, "build/ci/engineering-result.json"));
        planned = StageInput(exporter, commit, exportEnvironment);
        Assert.True(planned.Exit == 0, planned.Text);
        foreach (var stage in new[] { "build", "engineering" })
        {
            var restored = Workflow(exporter, "restore", stage, commit, archives[stage], exportEnvironment);
            Assert.True(restored.Exit == 0, restored.Text);
        }
        Assert.Equal(original.Candidate, CommonExecutionEvidence.ValidateEngineering(exporter).Candidate);
        Assert.False(Directory.Exists(Path.Combine(exporter, CommonExecutionEvidence.TestSeedPath)));
        Assert.False(Directory.Exists(Path.Combine(exporter, CommonExecutionEvidence.CheckSeedPath("engineering"))));
        var keys = Python(exporter, repository, ["keys", "--repository", exporter, "--stage", "engineering"], exportEnvironment);
        Assert.True(keys.Exit == 0, keys.Text);
        var deadline = CacheWithFixedClock(exporter, repository, "cache_deadline",
            ["begin", "--repository", exporter, "--stage", "engineering", "--job-timeout-minutes", "10"], exportEnvironment);
        Assert.True(deadline.Exit == 0, deadline.Text);
        Assert.Contains("\"cache_allowed\": true", deadline.Text, StringComparison.Ordinal);
        var snapshot = CacheWithFixedClock(exporter, repository, "lean_actions", snapshotArguments, exportEnvironment);
        AssertReceipt(snapshot, "snapshot");
        Assert.Equal("true", Key(snapshot.Text, "engineering_ready"));
        Assert.Equal("7", Key(snapshot.Text, "save_timeout_minutes"));
        var cached = Path.Combine(exporter, "build/lean-cache/engineering");
        var key = JsonNode.Parse(File.ReadAllText(Path.Combine(cached, "manifest.json")))!["key"]!.GetValue<string>();
        Assert.Equal(Key(keys.Text, "engineering_key"), key);
        var consumer = targets[1];
        var consumerEnvironment = IsolatedEnvironment(consumer, "82");
        // The upstream artifact retains its original execution identity.
        var restoredBuild = Workflow(consumer, "restore", "build", commit, archives["build"], IsolatedEnvironment(consumer, "81"));
        Assert.True(restoredBuild.Exit == 0, restoredBuild.Text);
        CopyDirectory(cached, Path.Combine(consumer, "build/lean-cache/engineering"));
        AssertReceipt(Python(consumer, repository, ["restore", "--repository", consumer, "--layers", "engineering", "--engineering-key", key], consumerEnvironment), "restored");
        var accepted = CommonExecutionEvidence.BeginChecks(consumer, "engineering", CommonExecutionEvidence.ValidateBuild(consumer), TextWriter.Null);
        foreach (var id in accepted.Ids)
        {
            Assert.False(accepted.IsSelected(id), id);
            accepted.Run(id, () => throw new InvalidOperationException("transport must not rerun " + id));
        }
        foreach (var unit in accepted.Seal().Units)
        {
            var prior = checks.Units.Single(row => row.Id == unit.Id);
            Assert.Equal("reused", unit.Status);
            Assert.Equal(prior.ExecutionCandidate, unit.ExecutionCandidate);
            Assert.Equal(prior.ExecutionRound, unit.ExecutionRound);
            Assert.Equal(prior.Operations, unit.Operations);
            Assert.Equal(prior.Materials, unit.Materials);
        }
        Assert.Equal(0, Program.RunCurrentTests(consumer, (_, _) => throw new InvalidOperationException("transport must not rerun tests"), TextWriter.Null));
        Assert.Equal(tests.Projects.Select(project => project with { Status = "reused" }), CommonExecutionEvidence.ValidateTests(consumer).Projects);
        var before = Inventory(cached);
        File.AppendAllText(Path.Combine(exporter, tests.Materials[0].Path), "corrupt evidence\n");
        var rejected = Workflow(exporter, "verify", "engineering", commit, archives["engineering"], exportEnvironment);
        Assert.True(rejected.Exit == 2, rejected.Text);
        var failed = CacheWithFixedClock(exporter, repository, "lean_actions", snapshotArguments, exportEnvironment);
        AssertReceipt(failed, "save-failed");
        Assert.Contains("engineering_ready=false", failed.Text, StringComparison.Ordinal);
        Assert.Equal(before, Inventory(cached));
        foreach (var target in targets)
            foreach (var path in new[] { ".lake", "build/absent-elan", "build/absent-packages" })
                Assert.False(Directory.Exists(Path.Combine(target, path)), path);
        Assert.Empty(Directory.GetFileSystemEntries(producer.Root));
        var commands = File.ReadAllLines(calls);
        Assert.Equal(7, commands.Length);
        Assert.All(commands, command => Assert.Contains("StrataLint.EngineeringScope.dll transport-", command, StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("engineering")]
    [InlineData("current")]
    public void NativeSeedPythonActionsRoundTripAcrossDistinctRoots(string stage)
    {
        if (OperatingSystem.IsWindows()) throw Xunit.Sdk.SkipException.ForSkip("native tar transport fixture is unsupported on Windows");
        using var fixture = Prepare(stage);
        var repository = TestRepositoryLayout.FindRoot();
        var commit = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD");
        var environment = Environment(commit, fixture.Root, "17", "2");
        var sourceChecks = CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath(stage));
        var sourceTests = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath);
        var sourceTrx = sourceTests.Materials.ToDictionary(material => material.Path,
            material => File.ReadAllBytes(Path.Combine(fixture.Root, material.Path)), StringComparer.Ordinal);
        var snapshot = Python(fixture.Root, repository, ["snapshot", "--repository", fixture.Root,
            "--layers", stage], environment);
        Assert.True(snapshot.Exit == 0, snapshot.Text);
        Assert.True(snapshot.Text.Contains("\"status\": \"snapshot\"", StringComparison.Ordinal), snapshot.Text);

        var target = Path.Combine(fixture.Root, "destination");
        SharedBuildContractTests.Git(fixture.Root, "clone", "--quiet", "--no-hardlinks", fixture.Root, target);
        CopyDirectory(Path.Combine(fixture.Root, "tools/StrataLint.EngineeringScope/bin/Release/net10.0"),
            Path.Combine(target, "tools/StrataLint.EngineeringScope/bin/Release/net10.0"));
        CopyDirectory(Path.Combine(fixture.Root, "build/lean-cache", stage),
            Path.Combine(target, "build/lean-cache", stage));
        Directory.CreateDirectory(Path.Combine(target, "build/ci"));
        var buildRecord = CommonExecutionEvidence.Read<CommonStageRecord>(fixture.Root, CommonExecutionEvidence.BuildPath);
        foreach (var material in buildRecord.Materials.Append(new ExecutionMaterial(CommonExecutionEvidence.BuildPath,
                     CommonExecutionEvidence.Hash(Path.Combine(fixture.Root, CommonExecutionEvidence.BuildPath)))))
        {
            var source = Path.Combine(fixture.Root, material.Path);
            var destination = Path.Combine(target, material.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(source, destination, overwrite: true);
        }
        var currentEvidence = Path.Combine(fixture.Root, "build/ci/current.json");
        if (File.Exists(currentEvidence))
            File.Copy(currentEvidence, Path.Combine(target, "build/ci/current.json"), overwrite: true);
        foreach (var path in CommonExecutionEvidence.ReportPaths)
        {
            var source = Path.Combine(fixture.Root, path);
            if (File.Exists(source))
            {
                var destination = Path.Combine(target, path);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                File.Copy(source, destination, overwrite: true);
            }
        }
        var targetEnvironment = Environment(commit, target, "18", "1");
        var key = Key(Python(fixture.Root, repository, ["keys", "--repository", fixture.Root,
            "--layers", stage], environment).Text, stage + "_key");
        var restore = Python(target, repository, ["restore", "--repository", target, "--layers", stage,
            "--" + stage + "-key", key], targetEnvironment);
        Assert.True(restore.Exit == 0, restore.Text);
        Assert.True(restore.Text.Contains("\"status\": \"restored\"", StringComparison.Ordinal), restore.Text);
        Assert.True(File.Exists(Path.Combine(target, "build/ci", stage + "-check-seed/checks.json")));
        Assert.True(File.Exists(Path.Combine(target, "build/ci/build.json")));

        var importOutput = new StringWriter();
        Assert.Equal(0, Program.Run(["check-seed-import", "--repository", target, "--stage", stage],
            TestResultEvidence.Load, importOutput, importOutput));
        Assert.Contains("COMMON_CHECK_REUSED", importOutput.ToString(), StringComparison.Ordinal);
        var importedChecks = CommonExecutionEvidence.Read<CommonCheckRecord>(target, CommonExecutionEvidence.CheckSeedPath(stage) + "/checks.json");
        Assert.Equal(sourceChecks.Candidate, importedChecks.Candidate);
        Assert.Equal(sourceChecks.Round, importedChecks.Round);
        Assert.Equal(sourceChecks.Units.Select(unit => (unit.Id, unit.ExecutionCandidate, unit.ExecutionRound)),
            importedChecks.Units.Select(unit => (unit.Id, unit.ExecutionCandidate, unit.ExecutionRound)));
        if (stage == "engineering")
        {
            var importedTests = CommonExecutionEvidence.Read<TestExecutionRecord>(target, CommonExecutionEvidence.TestSeedPath + "/tests.json");
            Assert.Equal(sourceTests.Candidate, importedTests.Candidate);
            Assert.Equal(sourceTests.Round, importedTests.Round);
            Assert.Equal(sourceTests.Projects.Select(project => (project.Project, project.ExecutionCandidate, project.ExecutionRound)),
                importedTests.Projects.Select(project => (project.Project, project.ExecutionCandidate, project.ExecutionRound)));
        }
        foreach (var (path, bytes) in sourceTrx)
        {
            var imported = Path.Combine(target, path);
            if (stage == "engineering") Assert.True(File.Exists(imported), imported);
            if (File.Exists(imported)) Assert.Equal(bytes, File.ReadAllBytes(imported));
        }
    }

    [Theory]
    [InlineData("engineering")]
    [InlineData("current")]
    public void ActionsOuterInventoryCannotInstallMaterialOutsideNativeBundle(string stage) =>
        AssertRejectedActionsSeed(stage, "extra-material");

    [Theory]
    [InlineData("engineering", "[]")]
    [InlineData("engineering", "null")]
    [InlineData("current", "[]")]
    [InlineData("current", "null")]
    public void ActionsNonObjectTransportIsAnHonestMiss(string stage, string json) =>
        AssertRejectedActionsSeed(stage, json);

    private static void AssertRejectedActionsSeed(string stage, string damage)
    {
        using var fixture = Prepare(stage);
        var repository = TestRepositoryLayout.FindRoot();
        var commit = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD");
        var environment = Environment(commit, fixture.Root, "71", "1");
        AssertReceipt(Python(fixture.Root, repository,
            ["snapshot", "--repository", fixture.Root, "--layers", stage], environment), "snapshot");
        var target = Destination(fixture, "boundary");
        var cached = Path.Combine(target, "build/lean-cache", stage);
        CopyDirectory(Path.Combine(fixture.Root, "build/lean-cache", stage), cached);
        var manifestPath = Path.Combine(cached, "manifest.json");
        var manifest = JsonNode.Parse(File.ReadAllText(manifestPath))!.AsObject();
        var data = Path.Combine(cached, "data");
        var transportPath = CiTransport.ManifestPath(stage + "-seed");
        var collateral = ".gitignore";
        var sibling = CommonExecutionEvidence.RootPath + "/" + (stage == "engineering" ? "current" : "engineering") + ".json";
        File.WriteAllText(Path.Combine(target, sibling), "existing sibling evidence\n");
        var protectedPaths = new[] { collateral, sibling, CommonExecutionEvidence.BuildPath };
        var before = protectedPaths.ToDictionary(path => path, path => File.ReadAllBytes(Path.Combine(target, path)));
        var damagedPath = damage == "extra-material" ? collateral : transportPath;
        File.WriteAllText(Path.Combine(data, damagedPath), damage == "extra-material" ? "unaccepted cache collateral\n" : damage);
        // Keep the outer Actions row valid so only the native material boundary
        // (or the native transport root shape) can reject this seed.
        var entries = manifest["files"]!.AsArray().Select(item => item!.DeepClone()).ToList();
        entries.RemoveAll(item => item["path"]!.GetValue<string>() == damagedPath);
        entries.Add(JsonSerializer.SerializeToNode(new
        {
            path = damagedPath,
            sha256 = CommonExecutionEvidence.Hash(Path.Combine(data, damagedPath)),
            mode = OperatingSystem.IsWindows() ? 0 : (int)File.GetUnixFileMode(Path.Combine(data, damagedPath)),
        })!);
        manifest["files"] = new JsonArray(entries.OrderBy(item => item["path"]!.GetValue<string>(), StringComparer.Ordinal).ToArray());
        File.WriteAllText(manifestPath, manifest.ToJsonString() + "\n");
        if (damage == "extra-material")
        {
            var declared = CommonExecutionEvidence.Read<CiTransportRecord>(data, transportPath);
            Assert.DoesNotContain(declared.Materials, item => item.Path == collateral);
            // Verification of a bundle inside a larger root must remain valid.
            // This extra file is rejected by the copying adapter, not global verify.
            var native = SharedBuildContractTests.Process(target, "dotnet",
                [Path.Combine(target, CommonExecutionEvidence.RunnerPath), "transport-verify", "--repository", data,
                    "--stage", stage + "-seed", "--commit", commit, "--run-id", "71", "--run-attempt", "1"],
                environment, TestBudgets.LongWorkflowProcessHangGuard);
            Assert.True(native.Exit == 0, native.Text);
        }
        var result = Python(target, repository,
            ["restore", "--repository", target, "--layers", stage, "--" + stage + "-key", manifest["key"]!.GetValue<string>()], environment);
        var unchanged = before.All(item => item.Value.SequenceEqual(File.ReadAllBytes(Path.Combine(target, item.Key))));
        if (System.Environment.GetEnvironmentVariable("EXECUTION_SEED_EVIDENCE") is { Length: > 0 } evidence)
        {
            Directory.CreateDirectory(evidence);
            var label = stage + "-" + (damage == "extra-material" ? damage : damage == "[]" ? "array-root" : "null-root");
            File.WriteAllText(Path.Combine(evidence, label + ".json"), JsonSerializer.Serialize(new
            {
                stage, damage, result.Exit, result.Text, unchanged,
                before = before.ToDictionary(item => item.Key, item => Convert.ToHexStringLower(SHA256.HashData(item.Value))),
                after = protectedPaths.ToDictionary(path => path, path => CommonExecutionEvidence.Hash(Path.Combine(target, path))),
                outerManifest = manifest,
            }));
        }
        AssertReceipt(result, "miss");
        Assert.DoesNotContain("\"status\": \"restored\"", result.Text, StringComparison.Ordinal);
        Assert.True(unchanged, "optional seed changed candidate collateral or sibling evidence");
        Assert.False(File.Exists(Path.Combine(target, CommonExecutionEvidence.BundleListPath(stage + "-seed"))));
        Assert.False(Directory.Exists(Path.Combine(target, CommonExecutionEvidence.CheckSeedPath(stage))));
        CommonExecutionEvidence.ValidateBuild(target);
    }

    [Fact]
    public void CorruptExecutionSeedDoesNotClobberExistingBuildOrSiblingEvidence()
    {
        if (OperatingSystem.IsWindows()) throw Xunit.Sdk.SkipException.ForSkip("native tar transport fixture is unsupported on Windows");
        using var fixture = Prepare("engineering");
        var repository = TestRepositoryLayout.FindRoot();
        var commit = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD");
        var environment = Environment(commit, fixture.Root, "21", "1");
        Assert.Equal(0, Python(fixture.Root, repository, ["snapshot", "--repository", fixture.Root,
            "--layers", "engineering"], environment).Exit);
        var cached = Path.Combine(fixture.Root, "build/lean-cache/engineering");
        var data = Path.Combine(cached, "data");
        var material = Directory.GetFiles(data, "*", SearchOption.AllDirectories)
            .Single(path => path.EndsWith("/engineering-check-seed/checks.json", StringComparison.Ordinal));
        File.WriteAllText(material, "corrupt");
        var manifestPath = Path.Combine(cached, "manifest.json");
        var manifest = JsonNode.Parse(File.ReadAllText(manifestPath))!.AsObject();
        var files = manifest["files"]!.AsArray();
        var relative = Path.GetRelativePath(data, material).Replace('\\', '/');
        var entry = files.Single(item => item!["path"]!.GetValue<string>() == relative)!.AsObject();
        entry["sha256"] = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(material)));
        File.WriteAllText(manifestPath, manifest.ToJsonString(new JsonSerializerOptions { WriteIndented = true }) + "\n");
        var build = Path.Combine(fixture.Root, "build/ci/build.json");
        var sibling = Path.Combine(fixture.Root, "build/ci/current.json");
        File.WriteAllText(sibling, "valid sibling\n");
        var buildBytes = File.ReadAllBytes(build);
        var siblingBytes = File.ReadAllBytes(sibling);
        var key = Key(Python(fixture.Root, repository, ["keys", "--repository", fixture.Root,
            "--layers", "engineering"], environment).Text, "engineering_key");
        var result = Python(fixture.Root, repository, ["restore", "--repository", fixture.Root,
            "--layers", "engineering", "--engineering-key", key], environment);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("\"status\": \"miss\"", result.Text, StringComparison.Ordinal);
        Assert.Contains("native execution transport rejected staged seed", result.Text, StringComparison.Ordinal);
        Assert.Equal(buildBytes, File.ReadAllBytes(build));
        Assert.Equal(siblingBytes, File.ReadAllBytes(sibling));
    }

    [Theory]
    [InlineData("engineering")]
    [InlineData("current")]
    public void WorkflowAdapterSeedRoundTripAcceptsNewCandidateWithOriginalProvenance(string stage)
    {
        using var fixture = Prepare(stage);
        var commit = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD");
        var environment = Environment(commit, fixture.Root, "41", "2");
        var archive = Path.Combine(fixture.Root, "build", stage + "-seed.tgz");
        var packed = Workflow(fixture.Root, "pack", stage + "-seed", commit, archive, environment);
        Assert.True(packed.Exit == 0, packed.Text);
        Assert.Contains("status=packed", packed.Text, StringComparison.Ordinal);
        var target = Destination(fixture, "workflow-" + stage);
        var restored = Workflow(target, "restore", stage + "-seed", commit, archive, environment);
        Assert.True(restored.Exit == 0, restored.Text);
        Assert.Contains("status=verified", restored.Text, StringComparison.Ordinal);
        AssertAccepted(fixture.Root, target, stage, "workflow-" + stage);
    }

    [Fact]
    public void OptionalActionsMissesAndFailedSavePreserveAcceptedSeed()
    {
        using var fixture = Prepare("engineering");
        var repository = TestRepositoryLayout.FindRoot();
        var commit = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD");
        var environment = Environment(commit, fixture.Root, "51", "1");
        var snapshot = Python(fixture.Root, repository, ["snapshot", "--repository", fixture.Root, "--layers", "engineering"], environment);
        AssertReceipt(snapshot, "snapshot");
        var cached = Path.Combine(fixture.Root, "build/lean-cache/engineering");
        var before = Inventory(cached);
        var key = Key(Python(fixture.Root, repository, ["keys", "--repository", fixture.Root, "--layers", "engineering"], environment).Text, "engineering_key");
        var target = Destination(fixture, "optional");
        (int Exit, string Text) Restore(string matched) => Python(target, repository,
            ["restore", "--repository", target, "--layers", "engineering", "--engineering-key", matched], environment);
        var absent = Restore(key);
        AssertReceipt(absent, "miss");
        Assert.Contains("manifest.json", absent.Text, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(target, CommonExecutionEvidence.CheckSeedPath("engineering"))));
        CopyDirectory(cached, Path.Combine(target, "build/lean-cache/engineering"));
        var missingKey = Restore("");
        AssertReceipt(missingKey, "miss");
        Assert.Contains("Actions supplied no cache", missingKey.Text, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(target, CommonExecutionEvidence.CheckSeedPath("engineering"))));
        var foreign = Restore(key.Replace("0123456789012345678901234567890123456789", new string('a', 40), StringComparison.Ordinal));
        AssertReceipt(foreign, "miss");
        Assert.Contains("outside the selected partition", foreign.Text, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(target, CommonExecutionEvidence.CheckSeedPath("engineering"))));

        var pullRequest = new Dictionary<string, string>(environment) { ["GITHUB_EVENT_NAME"] = "pull_request" };
        AssertReceipt(Python(fixture.Root, repository, ["snapshot", "--repository", fixture.Root, "--layers", "engineering"], pullRequest), "save-disabled");
        Assert.Equal(before, Inventory(cached));
        var malformed = new Dictionary<string, string>(environment) { ["CANDIDATE_SHA"] = "malformed-supplied-candidate" };
        var invalid = Python(fixture.Root, repository, ["snapshot", "--repository", fixture.Root, "--layers", "engineering"], malformed);
        AssertReceipt(invalid, "save-failed");
        Assert.Contains("CANDIDATE_SHA must be a 40-character commit identity", invalid.Text, StringComparison.Ordinal);
        Assert.Contains("engineering_ready=false", invalid.Text, StringComparison.Ordinal);
        Assert.Equal(before, Inventory(cached));

        var accepted = CommonExecutionEvidence.Read<CommonStageRecord>(fixture.Root, CommonExecutionEvidence.EngineeringPath);
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.EngineeringPath,
            accepted with { Steps = accepted.Steps.Select(step => step with { Exit = 1 }).ToArray() });
        var required = Workflow(fixture.Root, "pack", "engineering", commit, Path.Combine(fixture.Root, "build/failed.tgz"), environment);
        Assert.Equal(2, required.Exit);
        Assert.Contains("CI_INPUT_FAILED", required.Text, StringComparison.Ordinal);
        var failedSave = Python(fixture.Root, repository, ["snapshot", "--repository", fixture.Root, "--layers", "engineering"], environment);
        AssertReceipt(failedSave, "save-failed");
        Assert.Contains("engineering_ready=false", failedSave.Text, StringComparison.Ordinal);
        Assert.Equal(before, Inventory(cached));
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateEngineering(fixture.Root));
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.EngineeringPath, accepted);
        // Copy again after both failed saves, so destination acceptance proves the retained cache.
        CopyDirectory(cached, Path.Combine(target, "build/lean-cache/engineering"));
        AssertReceipt(Restore(key), "restored");
        AssertAccepted(fixture.Root, target, "engineering", "optional");
    }

    [Fact]
    public void NativePackFailureRemovesInvocationTemporaryArchive()
    {
        using var fixture = Prepare("engineering");
        var accepted = CommonExecutionEvidence.Read<CommonStageRecord>(fixture.Root, CommonExecutionEvidence.EngineeringPath);
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.EngineeringPath,
            accepted with { Steps = accepted.Steps.Select(step => step with { Exit = 1 }).ToArray() });
        var parent = Path.Combine(fixture.Root, "build/persistent-staging");
        fixture.Write("build/persistent-staging/unrelated.tgz", "retain me");
        var commit = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD");
        // The Actions CLI's outer TemporaryDirectory would mask an invocation archive leak.
        // Call its real pack adapter with a persistent parent and the real native runner.
        var result = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B", "-c", """
            import pathlib, sys
            sys.path.insert(0, sys.argv[1])
            from lean_actions import actions_keys, snapshot_execution
            root, destination = map(pathlib.Path, sys.argv[2:])
            snapshot_execution(root, 'engineering', actions_keys(root), destination)
            """, Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree"), fixture.Root, Path.Combine(parent, "data")],
            Environment(commit, fixture.Root, "55", "1"), TestBudgets.LongWorkflowProcessHangGuard);
        Assert.NotEqual(0, result.Exit);
        Assert.Contains("ENGINEERING_TEST_PLAN_FAILED", result.Text, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFiles(parent, ".engineering-transport-*"));
        Assert.Equal("retain me", File.ReadAllText(Path.Combine(parent, "unrelated.tgz")));
    }

    [Fact]
    public void ConcurrentActionsSavesProduceUsableNativeSeedOrHonestMiss()
    {
        using var fixture = Prepare("engineering");
        var repository = TestRepositoryLayout.FindRoot();
        var commit = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD");
        var environment = Environment(commit, fixture.Root, "61", "1");
        fixture.Write("build/coordination/dotnet", """
            #!/usr/bin/env python3
            import os, socket, sys
            with socket.create_connection(('127.0.0.1', int(os.environ['SEED_BARRIER_PORT']))) as connection:
                connection.sendall((os.environ['GITHUB_RUN_ID'] + '\n').encode())
                if connection.recv(1) != b'G': raise RuntimeError('barrier did not release')
            os.execv(os.environ['SEED_REAL_DOTNET'], [os.environ['SEED_REAL_DOTNET'], *sys.argv[1:]])
            """);
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Path.Combine(fixture.Root, "build/coordination/dotnet"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var result = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B", "-c", """
            import os, pathlib, shutil, socket, subprocess, sys
            root, script = map(pathlib.Path, sys.argv[1:])
            environment = dict(os.environ, SEED_REAL_DOTNET=shutil.which('dotnet'))
            environment['PATH'] = str(root / 'build/coordination') + os.pathsep + environment['PATH']
            children, connections = [], []
            with socket.socket() as server:
                server.bind(('127.0.0.1', 0))
                server.listen(2)
                environment['SEED_BARRIER_PORT'] = str(server.getsockname()[1])
                try:
                    for run in ('61', '62'):
                        children.append(subprocess.Popen([sys.executable, '-B', str(script), 'snapshot',
                            '--repository', str(root), '--layers', 'engineering'],
                            env=dict(environment, GITHUB_RUN_ID=run), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True))
                    for _ in children:
                        connection, _ = server.accept()
                        connections.append(connection)
                        print('CONCURRENT_PACK_READY run=' + connection.makefile().readline().strip(), flush=True)
                    assert all(child.poll() is None for child in children)
                    for connection in connections: connection.sendall(b'G')
                    for child in children:
                        output, _ = child.communicate()
                        print(output, end='')
                        assert child.returncode == 0, output
                finally:
                    for connection in connections: connection.close()
                    for child in children:
                        if child.poll() is None: child.kill()
                        child.wait()
            """, fixture.Root, Path.Combine(repository, "tools/scripts/worktree/lean_actions.py")], environment,
            TestBudgets.LongWorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("CONCURRENT_PACK_READY run=61", result.Text, StringComparison.Ordinal);
        Assert.Contains("CONCURRENT_PACK_READY run=62", result.Text, StringComparison.Ordinal);
        var receipts = result.Text.Split('\n').Where(line => line.StartsWith("LEAN_ACTIONS_CACHE ", StringComparison.Ordinal))
            .Select(line => JsonNode.Parse(line["LEAN_ACTIONS_CACHE ".Length..])!["status"]!.ToString()).ToArray();
        Assert.Equal(2, receipts.Length);
        Assert.All(receipts, status => Assert.Contains(status, new[] { "snapshot", "save-failed" }));
        var target = Destination(fixture, "concurrent");
        var cached = Path.Combine(fixture.Root, "build/lean-cache/engineering");
        var key = "";
        if (Directory.Exists(cached))
        {
            CopyDirectory(cached, Path.Combine(target, "build/lean-cache/engineering"));
            var manifest = Path.Combine(cached, "manifest.json");
            if (File.Exists(manifest)) key = JsonNode.Parse(File.ReadAllText(manifest))!["key"]!.ToString();
        }
        var restore = Python(target, repository, ["restore", "--repository", target, "--layers", "engineering", "--engineering-key", key], environment);
        Assert.True(restore.Exit == 0, restore.Text);
        if (restore.Text.Contains("\"status\": \"restored\"", StringComparison.Ordinal))
            AssertAccepted(fixture.Root, target, "engineering", "concurrent");
        else
        {
            AssertReceipt(restore, "miss");
            var build = CommonExecutionEvidence.ValidateBuild(target);
            var checks = CommonExecutionEvidence.BeginChecks(target, "engineering", build, TextWriter.Null);
            Assert.All(checks.Ids, id => Assert.True(checks.IsSelected(id), id));
            foreach (var id in checks.Ids) checks.Run(id, () => new CheckWork(CommonCheckExecutionTests.Fixture.Work(id)));
            Assert.All(checks.Seal().Units, unit => Assert.Equal("executed", unit.Status));
        }
    }

    private static string Destination(CurrentExecutionContractTests.CandidateFixture fixture, string name)
    {
        var target = Path.Combine(fixture.Root, "build/destination-" + name);
        SharedBuildContractTests.Git(fixture.Root, "clone", "--quiet", "--no-hardlinks", fixture.Root, target);
        File.AppendAllText(Path.Combine(target, ".gitignore"), "# new accepted candidate\n");
        SharedBuildContractTests.Git(target, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qam", "new acceptance");
        CopyDirectory(Path.Combine(fixture.Root, "tools/StrataLint.EngineeringScope/bin/Release/net10.0"),
            Path.Combine(target, "tools/StrataLint.EngineeringScope/bin/Release/net10.0"));
        var sourceBuild = CommonExecutionEvidence.ValidateBuild(fixture.Root);
        foreach (var path in sourceBuild.Materials.Select(material => material.Path).Concat(CommonExecutionEvidence.ReportPaths))
        {
            var source = Path.Combine(fixture.Root, path);
            if (!File.Exists(source)) continue;
            var destination = Path.Combine(target, path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(source, destination, overwrite: true);
        }
        var build = CommonExecutionEvidence.SealBuild(target, CommonExecutionEvidence.Candidate(target),
            sourceBuild.Materials.Select(material => material.Path), sourceBuild.Steps);
        Assert.NotEqual(sourceBuild.Candidate, build.Candidate);
        Assert.NotEqual(sourceBuild.Round, build.Round);
        return target;
    }

    private static void AssertAccepted(string source, string target, string stage, string label)
    {
        var original = CommonExecutionEvidence.Read<CommonCheckRecord>(source, CommonExecutionEvidence.ChecksPath(stage));
        var build = CommonExecutionEvidence.ValidateBuild(target);
        var checks = CommonExecutionEvidence.BeginChecks(target, stage, build, TextWriter.Null);
        Assert.NotEmpty(checks.Ids);
        foreach (var id in checks.Ids)
        {
            Assert.False(checks.IsSelected(id), id);
            checks.Run(id, () => throw new InvalidOperationException("transported unit must be reused: " + id));
        }
        var accepted = checks.Seal();
        Assert.Equal(build.Candidate, accepted.Candidate);
        Assert.Equal(build.Round, accepted.Round);
        Assert.NotEqual(original.Candidate, accepted.Candidate);
        Assert.NotEqual(original.Round, accepted.Round);
        foreach (var unit in accepted.Units)
        {
            var prior = original.Units.Single(row => row.Id == unit.Id);
            Assert.Equal("reused", unit.Status);
            Assert.Equal(prior.ExecutionCandidate, unit.ExecutionCandidate);
            Assert.Equal(prior.ExecutionRound, unit.ExecutionRound);
            Assert.Equal(prior.Operations, unit.Operations);
            Assert.Equal(prior.Materials, unit.Materials);
        }
        TestExecutionRecord? tests = null;
        if (stage == "engineering")
        {
            Assert.Equal(0, Program.RunCurrentTests(target, (_, _) => throw new InvalidOperationException("transported test must be reused"), TextWriter.Null));
            tests = CommonExecutionEvidence.ValidateTests(target);
            var prior = CommonExecutionEvidence.ValidateTests(source);
            Assert.Equal(build.Candidate, tests.Candidate);
            Assert.Equal(build.Round, tests.Round);
            Assert.Equal(prior.Projects.Select(project => project with { Status = "reused" }), tests.Projects);
            Assert.Equal(prior.Materials, tests.Materials);
            foreach (var material in prior.Materials)
                Assert.Equal(File.ReadAllBytes(Path.Combine(source, material.Path)), File.ReadAllBytes(Path.Combine(target, material.Path)));
        }
        var originalStage = CommonExecutionEvidence.Read<CommonStageRecord>(source,
            stage == "engineering" ? CommonExecutionEvidence.EngineeringPath : CommonExecutionEvidence.CurrentPath);
        if (stage == "engineering") CommonExecutionEvidence.SealEngineering(target, build, originalStage.Steps);
        else CommonExecutionEvidence.SealCurrent(target, build, originalStage.Steps);
        var sealedStage = stage == "engineering" ? CommonExecutionEvidence.ValidateEngineering(target) : CommonExecutionEvidence.ValidateCurrent(target);
        Assert.Equal(build.Candidate, sealedStage.Candidate);
        Assert.Equal(build.Round, sealedStage.Round);
        if (System.Environment.GetEnvironmentVariable("EXECUTION_SEED_EVIDENCE") is { Length: > 0 } evidence)
        {
            Directory.CreateDirectory(evidence);
            File.WriteAllText(Path.Combine(evidence, label + "-acceptance.json"), JsonSerializer.Serialize(new { original, accepted, tests, sealedStage }));
            foreach (var material in tests?.Materials ?? [])
            {
                var path = Path.Combine(evidence, label, material.Path);
                Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                File.Copy(Path.Combine(target, material.Path), path, overwrite: true);
            }
        }
    }

    private static (int Exit, string Text) Workflow(string root, string command, string stage, string commit, string archive, Dictionary<string, string> environment) =>
        SharedBuildContractTests.Process(root, "python3", ["-B", Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow/ci.py"),
            command, "--repository", root, "--stage", stage, "--commit", commit, "--archive", archive], environment,
            TestBudgets.LongWorkflowProcessHangGuard);

    private static (int Exit, string Text) StageInput(string root, string commit, Dictionary<string, string> environment) =>
        SharedBuildContractTests.Process(root, "python3", ["-B", Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow/ci.py"),
            "stage-input", "--repository", root, "--stage", "engineering", "--commit", commit], environment,
            TestBudgets.LongWorkflowProcessHangGuard);

    private static (int Exit, string Text) CacheWithFixedClock(string root, string repository, string module, string[] arguments,
        Dictionary<string, string> environment) => SharedBuildContractTests.Process(root, "python3", ["-B", "-c", """
            import importlib, sys, types
            sys.path.insert(0, sys.argv.pop(1))
            import cache_deadline
            # Only the deadline's two clock dependencies are deterministic.
            # Its CLI, metadata validation, state writer/reader and the native
            # snapshot worker execute normally, with their real hang guards.
            cache_deadline.time = types.SimpleNamespace(time=lambda: 1767225600, monotonic=lambda: 1000)
            command = importlib.import_module(sys.argv.pop(1))
            raise SystemExit(command.main())
            """, Path.Combine(repository, "tools/scripts/worktree"), module, .. arguments], environment,
            TestBudgets.LongWorkflowProcessHangGuard);

    private static void AssertReceipt((int Exit, string Text) result, string status)
    {
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("\"status\": \"" + status + "\"", result.Text, StringComparison.Ordinal);
    }

    private static (string Path, string Hash, int Mode)[] Inventory(string root) => Directory.GetFiles(root, "*", SearchOption.AllDirectories)
        .Order(StringComparer.Ordinal).Select(path => (Path.GetRelativePath(root, path), CommonExecutionEvidence.Hash(path),
            OperatingSystem.IsWindows() ? 0 : (int)File.GetUnixFileMode(path))).ToArray();

    private static CurrentExecutionContractTests.CandidateFixture Prepare(string stage, bool plannedEngineering = false)
    {
        var fixture = new CurrentExecutionContractTests.CandidateFixture();
        fixture.Write("lean-toolchain", "leanprover/lean4:v4.19.0\n");
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\",\"dir\":\".lake/packages/mathlib\"}]}\n");
        fixture.Write("lakefile.toml", "name = 'fixture'\n");
        if (plannedEngineering)
        {
            fixture.Write("Meta/FILEMAP.toml", """
                schema_version = 4
                resources = [
                  { id = "build", stage = "build", owner = "tools/tests/First/First.csproj", prerequisites = [], tools = [], cache_layers = [], cache_activation = {}, materials = ["Meta/ci-checks.json", "Meta/ci-resources.json", "Meta/engineering-projects.json"] },
                  { id = "engineering", stage = "engineering", owner = "tools/tests/First/First.csproj", prerequisites = ["build"], tools = ["dotnet"], cache_layers = ["engineering"], cache_activation = { engineering = "stage-start" }, materials = [] }
                ]
                [residence_policy]
                case_id = "fixture"
                desired = "registered"
                known_violation_count = 0
                status = "active"
                [[files]]
                pattern = "**"
                require = ["engineering"]
                kind = "program"
                admission_plane = "judge"
                produced_by = "none"
                consumed_by = ["test"]
                verified_by = ["test"]
                artifact_id = "none"
                runtime_disposition = "committed-source"
                """ + "\n");
            fixture.Write("Meta/ci-resources.json", JsonSerializer.Serialize(new { schema = "ci-resource-execution-v1", resources = new[]
            {
                new { id = "build", projects = Array.Empty<string>(), checks = Array.Empty<string>(), steps = Array.Empty<string>() },
                new { id = "engineering", projects = new[] { CurrentExecutionContractTests.CandidateFixture.First, CurrentExecutionContractTests.CandidateFixture.Second },
                    checks = new[] { "banned-api-proof", "capability-proof", "selftest-pair" }, steps = Array.Empty<string>() },
            } }));
            SharedBuildContractTests.Git(fixture.Root, "add", "Meta/FILEMAP.toml", "Meta/ci-resources.json");
        }
        SharedBuildContractTests.Git(fixture.Root, "add", "lean-toolchain", "lake-manifest.json", "lakefile.toml");
        SharedBuildContractTests.Git(fixture.Root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "seed inputs");
        fixture.Build();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, directory) => { fixture.WriteTrx(directory, "Passed"); return 0; }, TextWriter.Null));
        fixture.Write("build/ci/fixture-executable", "#!/bin/sh\nexit 0\n");
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Path.Combine(fixture.Root, "build/ci/fixture-executable"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var candidate = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath).Candidate;
        CiTransportTests.SealEngineering(fixture.Root, candidate, ["build/ci/fixture-executable"], CommonExecutionEvidence.EngineeringSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/fixture-executable")).ToArray());
        if (stage == "current")
        {
            CiTransportTests.Report(fixture.Root);
            CheckEvidenceFixture.Seal(fixture.Root, "current", CommonExecutionEvidence.ValidateBuild(fixture.Root));
            CommonExecutionEvidence.SealCurrent(fixture.Root, CommonExecutionEvidence.ValidateBuild(fixture.Root), CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/fixture-executable")).ToArray());
        }
        Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, stage, TextWriter.Null));
        var output = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/StrataLint.EngineeringScope/bin/Release/net10.0");
        CopyDirectory(output, Path.Combine(fixture.Root, "tools/StrataLint.EngineeringScope/bin/Release/net10.0"));
        return fixture;
    }

    private static Dictionary<string, string> Environment(string commit, string root, string run, string attempt) => new()
    {
        ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev", ["GITHUB_RUN_ID"] = run,
        ["GITHUB_RUN_ATTEMPT"] = attempt, ["CANDIDATE_SHA"] = commit, ["GITHUB_REPOSITORY"] = "fixture/repo",
        ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "true",
        ["GITHUB_OUTPUT"] = Path.Combine(root, "build/actions-output")
    };

    private static (int Exit, string Text) Python(string root, string repository, string[] args, Dictionary<string, string> environment) =>
        SharedBuildContractTests.Process(root, "python3", new[] { "-B", Path.Combine(repository, "tools/scripts/worktree/lean_actions.py") }.Concat(args).ToArray(), environment,
            TestBudgets.LongWorkflowProcessHangGuard);

    private static void CopyDirectory(string source, string destination)
    {
        foreach (var directory in Directory.GetDirectories(source, "*", SearchOption.AllDirectories))
            Directory.CreateDirectory(Path.Combine(destination, Path.GetRelativePath(source, directory)));
        foreach (var file in Directory.GetFiles(source, "*", SearchOption.AllDirectories))
            File.Copy(file, Path.Combine(destination, Path.GetRelativePath(source, file)), overwrite: true);
    }

    private static string Key(string text, string name) => text.Split('\n', StringSplitOptions.RemoveEmptyEntries)
        .Single(line => line.StartsWith(name + "=", StringComparison.Ordinal))[(name.Length + 1)..].Trim();
}
