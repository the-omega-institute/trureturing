using System.Text.Json;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class EngineeringScopeProgramTests
{
    [Fact]
    public void MultiCommitPushIncludesEarlierInputChanges() => WithRange(root =>
    {
        var before = GitText(root, "rev-parse", "HEAD");
        WriteFile(root, ProductFeature, "internal class Changed { }\n");
        Commit(root);
        WriteFile(root, "notes/latest.md", "second commit\n");
        Commit(root);
        var result = Plan(root, before);
        Assert.Equal(0, result.ExitCode);
        Assert.Contains(ProductTestsProject, result.Output, StringComparison.Ordinal);
    });

    [Fact]
    public void NonAncestorPushIncludesDeletionAndBothRenameEnds() => WithRange(root =>
    {
        var before = GitText(root, "rev-parse", "HEAD");
        RunGit(root, "checkout", "--orphan", "replacement");
        RunGit(root, "rm", "--cached", "-r", ".");
        TemporaryFileSystem.File.Delete(Path.Combine(root, ProductFeature));
        WriteFile(root, "notes/renamed.md", "internal class Feature { }\n");
        Commit(root);
        var result = Plan(root, before);
        Assert.Equal(0, result.ExitCode);
        Assert.Contains(ProductTestsProject, result.Output, StringComparison.Ordinal);
        Assert.Contains(ProductFeature, result.Output, StringComparison.Ordinal);
        Assert.Contains("notes/renamed.md", result.Output, StringComparison.Ordinal);
    });

    [Fact]
    public void InitialPushSelectsCompleteRegisteredCurrentInputs() => WithRange(root =>
    {
        var result = Plan(root, new string('0', 40));
        Assert.Equal(0, result.ExitCode);
        Assert.Contains(ProductTestsProject, result.Output, StringComparison.Ordinal);
        Assert.Contains("initial", result.Output, StringComparison.Ordinal);
    });

    [Fact]
    public void MissingInputRegistrationFailsBeforeExecution() => WithRange(root =>
    {
        var before = GitText(root, "rev-parse", "HEAD");
        WriteFile(root, "tools/unregistered/Input.cs", "new input\n");
        Commit(root);
        var result = Plan(root, before);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("tools/unregistered/Input.cs", result.Error, StringComparison.Ordinal);
        Assert.Contains("missing input registration", result.Error, StringComparison.Ordinal);
    });

    [Fact]
    public void ConflictingInputRegistrationFailsBeforeExecution() => WithRange(root =>
    {
        var before = GitText(root, "rev-parse", "HEAD");
        var path = Path.Combine(root, EngineeringManifestPath);
        var manifest = System.Text.Json.Nodes.JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(path))!;
        manifest["inputs"]!.AsArray().Add(JsonSerializer.SerializeToNode(new { patterns = new[] { "notes/**" }, projects = Array.Empty<string>() }));
        TemporaryFileSystem.File.WriteAllText(path, manifest.ToJsonString());
        WriteFile(root, "notes/latest.md", "changed\n");
        Commit(root);
        var result = Plan(root, before);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("notes/latest.md", result.Error, StringComparison.Ordinal);
        Assert.Contains("conflicting input registrations", result.Error, StringComparison.Ordinal);
    });

    [Theory]
    [InlineData("missing")]
    [InlineData("malformed")]
    [InlineData("head-mismatch")]
    [InlineData("deletion")]
    public void InvalidPushRangeFailsExplicitly(string defect) => WithRange(root =>
    {
        var head = GitText(root, "rev-parse", "HEAD");
        var before = defect == "malformed" ? "HEAD^1" : new string('1', 40);
        if (defect is "head-mismatch" or "deletion") before = head;
        var after = defect == "head-mismatch" ? new string('2', 40)
            : defect == "deletion" ? new string('0', 40) : head;
        var result = Plan(root, before, after);
        Assert.Equal(2, result.ExitCode);
        Assert.DoesNotContain("ENGINEERING_TEST_PLAN state=", result.Output, StringComparison.Ordinal);
    });

    [Fact]
    public void RegisteredNoResourcePushReportsNotRequired() => WithRange(root =>
    {
        var before = GitText(root, "rev-parse", "HEAD");
        WriteFile(root, "notes/latest.md", "no engineering resource\n");
        Commit(root);
        var result = Plan(root, before);
        Assert.Equal(0, result.ExitCode);
        Assert.Contains("state=none", result.Output, StringComparison.Ordinal);
        Assert.Contains("not-required", result.Output, StringComparison.Ordinal);
    });

    [Fact]
    public void DirtyPushCandidateIncludesUncommittedRegisteredInput() => WithRange(root =>
    {
        var before = GitText(root, "rev-parse", "HEAD");
        WriteFile(root, ProductFeature, "internal class Dirty { }\n");
        var result = Plan(root, before);
        Assert.Equal(0, result.ExitCode);
        Assert.Contains(ProductTestsProject, result.Output, StringComparison.Ordinal);
    });

    [Theory]
    [InlineData("valid", 0)]
    [InlineData("wrong-base", 2)]
    [InlineData("dirty", 2)]
    public void PullRequestRequiresCleanMergeAndItsFirstParent(string scenario, int expected) => WithRange(root =>
    {
        var before = GitText(root, "rev-parse", "HEAD");
        WriteFile(root, ProductFeature, "internal class MergeChange { }\n");
        Commit(root);
        var branchHead = GitText(root, "rev-parse", "HEAD");
        var tree = GitText(root, "rev-parse", "HEAD^{tree}");
        var merge = GitText(root, "commit-tree", tree, "-p", before, "-p", branchHead, "-m", "merge fixture");
        RunGit(root, "checkout", "--detach", merge);
        if (scenario == "dirty") WriteFile(root, ProductFeature, "internal class DirtyMerge { }\n");
        var result = Plan(root, scenario == "wrong-base" ? branchHead : before, eventKind: "pull-request");
        Assert.True(result.ExitCode == expected, result.Error);
        if (expected == 0) Assert.Contains(ProductTestsProject, result.Output, StringComparison.Ordinal);
        else Assert.DoesNotContain("ENGINEERING_TEST_PLAN state=", result.Output, StringComparison.Ordinal);
    });

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InitialNoResourceRequiresCompleteRegistration(bool missing)
    {
        var root = TemporaryFileSystem.Directory.CreateTempSubdirectory("initial-no-resource-").FullName;
        try
        {
            RunGit(root, "init", "--quiet");
            RunGit(root, "config", "user.email", "initial@example.invalid");
            RunGit(root, "config", "user.name", "Initial fixture");
            WriteAdmissionPlaneFileMap(root, ("notes/**", "content"), (FileMapPath, "judge"));
            WriteFile(root, EngineeringManifestPath, "{\"schema_version\":1,\"projects\":[],\"inputs\":[]}");
            CompleteRegistration(root);
            WriteFile(root, missing ? "missing.txt" : "notes/input.md", "registered resource-free data\n");
            Commit(root);
            var result = Plan(root, new string('0', 40));
            Assert.True(result.ExitCode == (missing ? 2 : 0), result.Error);
            if (missing) Assert.Contains("missing.txt", result.Error, StringComparison.Ordinal);
            else Assert.Contains("not-required", result.Output, StringComparison.Ordinal);
        }
        finally { TemporaryFileSystem.Directory.Delete(root, recursive: true); }
    }

    [Fact]
    public void UntrackedProjectCannotUseRegisteredNoResourceCoverage() => WithRange(root =>
    {
        var head = GitText(root, "rev-parse", "HEAD");
        WriteFile(root, "notes/Rogue.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\" />");
        var result = Plan(root, head);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("notes/Rogue.csproj: missing project registration", result.Error, StringComparison.Ordinal);
    });

    [Fact]
    public void ChangedProjectMaterialRequiresUpdatedDeclaration() => WithRange(root =>
    {
        var head = GitText(root, "rev-parse", "HEAD");
        WriteFile(root, ProductProject, "<Project Sdk=\"Microsoft.NET.Sdk\" />");
        var result = Plan(root, head);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains(ProductProject + ": registered project sha256 differs", result.Error, StringComparison.Ordinal);
    });

    private static void WithRange(Action<string> test)
    {
        var root = TemporaryFileSystem.Directory.CreateTempSubdirectory("engineering-range-").FullName;
        try
        {
            RunGit(root, "init", "--quiet");
            RunGit(root, "config", "user.email", "range@example.invalid");
            RunGit(root, "config", "user.name", "Range Tests");
            WriteGateInfrastructure(root);
            WriteProductProjects(root);
            WriteFile(root, ProductFeature, "internal class Feature { }\n");
            CompleteRegistration(root);
            Commit(root);
            test(root);
        }
        finally { TemporaryFileSystem.Directory.Delete(root, recursive: true); }
    }

    private static void Commit(string root)
    {
        RunGit(root, "add", ".");
        RunGit(root, "commit", "--quiet", "--allow-empty", "-m", "fixture");
    }

    private static (int ExitCode, string Output, string Error) Plan(string root, string before, string? head = null, string eventKind = "push")
    {
        using var output = new StringWriter();
        using var error = new StringWriter();
        var code = Program.Run(["--repository", root, "--event", eventKind, eventKind == "push" ? "--before" : "--base", before,
            "--head", head ?? GitText(root, "rev-parse", "HEAD"), "--plan-only", "1"],
            TestResultEvidence.Load, output, error);
        return (code, output.ToString(), error.ToString());
    }
}
