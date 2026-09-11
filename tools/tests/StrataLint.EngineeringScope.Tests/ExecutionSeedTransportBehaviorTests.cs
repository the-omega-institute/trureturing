using System.Diagnostics;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class ExecutionSeedTransportBehaviorTests
{
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

    private static CurrentExecutionContractTests.CandidateFixture Prepare(string stage)
    {
        var fixture = new CurrentExecutionContractTests.CandidateFixture();
        fixture.Write("lean-toolchain", "leanprover/lean4:v4.19.0\n");
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\",\"dir\":\".lake/packages/mathlib\"}]}\n");
        fixture.Write("lakefile.toml", "name = 'fixture'\n");
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
