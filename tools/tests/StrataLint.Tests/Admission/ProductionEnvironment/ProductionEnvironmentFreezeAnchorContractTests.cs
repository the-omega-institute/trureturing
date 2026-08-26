using System.Diagnostics;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CheckWithProductionGitRejectsAddedFreezeAnchoredToReachableNonAncestor()
    {
        using var repository = new TemporaryDirectory();
        using var reports = new TemporaryDirectory();
        var fixture = CreateProductionFreezeFixture(repository.Path, useNonAncestorAnchor: true);

        Assert.Equal(1, GitExitCode(
            repository.Path,
            "merge-base",
            "--is-ancestor",
            fixture.AnchorCommit,
            "HEAD"));

        var diagnostic = AssertFrozenAnchorRejection(CheckProductionFreezeFixture(
            repository.Path,
            reports,
            fixture));

        Assert.Contains("is not an ancestor of candidate HEAD", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("malformed-anchor", "malformed Git object reference")]
    [InlineData("wrong-object-type", "has type tree; expected blob")]
    [InlineData("commit-tree-mismatch", "does not resolve to base_tree_oid")]
    [InlineData("descriptor-not-in-tree", "descriptor selector does not resolve")]
    [InlineData("supporting-blob-unreachable", "supporting blob is not reachable")]
    [InlineData("forged-statement", "does not match recomputed material")]
    [InlineData("invalid-case-id", "does not match recomputed material")]
    public void IncrementalAdmissionRejectsFreezeBoundaryViolation(
        string violation,
        string expectedMessage)
    {
        using var repository = new TemporaryDirectory();
        using var reports = new TemporaryDirectory();
        var fixture = CreateProductionFreezeFixture(
            repository.Path,
            useNonAncestorAnchor: false,
            violation);

        var diagnostic = AssertFrozenAnchorRejection(CheckProductionFreezeFixture(
            repository.Path,
            reports,
            fixture));

        Assert.Contains(expectedMessage, diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckWithProductionGitAcceptsCanonicalPhaseAFreezeAnchor()
    {
        using var repository = new TemporaryDirectory();
        using var reports = new TemporaryDirectory();
        var fixture = CreateProductionFreezeFixture(repository.Path, useNonAncestorAnchor: false);

        Assert.Equal(0, GitExitCode(
            repository.Path,
            "merge-base",
            "--is-ancestor",
            fixture.AnchorCommit,
            "HEAD"));

        var outcome = CheckProductionFreezeFixture(repository.Path, reports, fixture);

        Assert.True(
            outcome is AdmissionOutcome.Admitted,
            RenderOutcome(outcome));
    }

    private static ProductionFreezeFixture CreateProductionFreezeFixture(
        string repositoryRoot,
        bool useNonAncestorAnchor,
        string? violation = null)
    {
        var fixture = AddedFrozenRingFixture();
        var addedFreezePaths = AddedLedgerPaths(fixture);
        var targetFreezePath = AddedFreezePathFor(fixture, RuleFixture.RingPath);
        var phaseAFiles = fixture.Files
            .Where(item => !addedFreezePaths.Contains(item.Key, StringComparer.Ordinal))
            .ToDictionary(static item => item.Key, static item => item.Value, StringComparer.Ordinal);

        InitializeRepository(repositoryRoot);
        WriteFiles(repositoryRoot, fixture.Baseline);
        ReviewRegressionTests.RunGit(repositoryRoot, "add", ".");
        ReviewRegressionTests.RunGit(repositoryRoot, "commit", "-m", "protected base");
        var protectedBase = GitText(repositoryRoot, "rev-parse", "HEAD");
        var protectedTree = GitText(repositoryRoot, "rev-parse", "HEAD^{tree}");

        ReviewRegressionTests.RunGit(repositoryRoot, "checkout", "-b", "foreign", protectedBase);
        const string foreignPath = "foreign-only.txt";
        File.WriteAllText(
            Path.Combine(repositoryRoot, foreignPath),
            "reachable outside the candidate history\n",
            new UTF8Encoding(false));
        ReviewRegressionTests.RunGit(repositoryRoot, "add", ".");
        ReviewRegressionTests.RunGit(repositoryRoot, "commit", "-m", "foreign blob owner");
        var foreignBlob = GitText(repositoryRoot, "rev-parse", $"HEAD:{foreignPath}");

        ReviewRegressionTests.RunGit(repositoryRoot, "checkout", "-b", "side-anchor", protectedBase);
        WriteFiles(repositoryRoot, phaseAFiles);
        ReviewRegressionTests.RunGit(repositoryRoot, "add", ".");
        ReviewRegressionTests.RunGit(repositoryRoot, "commit", "-m", "side phase A");
        var sideCommit = GitText(repositoryRoot, "rev-parse", "HEAD");
        var sideTree = GitText(repositoryRoot, "rev-parse", "HEAD^{tree}");

        ReviewRegressionTests.RunGit(repositoryRoot, "checkout", "-b", "candidate", protectedBase);
        WriteFiles(repositoryRoot, phaseAFiles);
        ReviewRegressionTests.RunGit(repositoryRoot, "add", ".");
        ReviewRegressionTests.RunGit(repositoryRoot, "commit", "-m", "candidate phase A");
        var phaseACommit = GitText(repositoryRoot, "rev-parse", "HEAD");
        var phaseATree = GitText(repositoryRoot, "rev-parse", "HEAD^{tree}");
        Assert.Equal(sideTree, phaseATree);
        Assert.NotEqual(sideCommit, phaseACommit);

        var anchorCommit = useNonAncestorAnchor ? sideCommit : phaseACommit;
        var anchorTree = useNonAncestorAnchor ? sideTree : phaseATree;
        foreach (var addedFreezePath in addedFreezePaths)
        {
            RewriteAddedFreeze(
                fixture,
                addedFreezePath,
                anchorCommit,
                anchorTree,
                protectedTree,
                foreignPath,
                foreignBlob,
                string.Equals(addedFreezePath, targetFreezePath, StringComparison.Ordinal)
                    ? violation
                    : null);
        }
        WriteFiles(repositoryRoot, fixture.Files);
        ReviewRegressionTests.RunGit(repositoryRoot, "add", ".");
        ReviewRegressionTests.RunGit(repositoryRoot, "commit", "-m", "candidate phase B freeze");

        return new ProductionFreezeFixture(fixture, protectedBase, anchorCommit);
    }

    private static void RewriteAddedFreeze(
        RuleFixture fixture,
        string oldPath,
        string anchorCommit,
        string anchorTree,
        string protectedTree,
        string foreignPath,
        string foreignBlob,
        string? violation)
    {
        var root = JsonNode.Parse(fixture.Files[oldPath])!.AsObject();
        var payload = root["payload"]!.AsObject();
        var input = payload["input"]!.AsObject();
        input["base_commit_oid"] = TagGitOid(anchorCommit);
        input["base_tree_oid"] = TagGitOid(anchorTree);

        switch (violation)
        {
            case null:
                break;
            case "malformed-anchor":
                input["base_commit_oid"] = "not-an-anchor";
                break;
            case "wrong-object-type":
                input["descriptor_blob_oid"] = TagGitOid(anchorTree);
                break;
            case "commit-tree-mismatch":
                input["base_tree_oid"] = TagGitOid(protectedTree);
                break;
            case "descriptor-not-in-tree":
                input["descriptor_selector"] = foreignPath;
                input["descriptor_blob_oid"] = TagGitOid(foreignBlob);
                break;
            case "supporting-blob-unreachable":
                var supporting = input["supporting_blob_oids"]!.AsArray()
                    .Select(static item => item!.GetValue<string>())
                    .Append(TagGitOid(foreignBlob))
                    .Order(StringComparer.Ordinal)
                    .Select(static oid => JsonValue.Create(oid))
                    .ToArray();
                input["supporting_blob_oids"] = new JsonArray(supporting);
                break;
            case "forged-statement":
                payload["statement_id"] = "sha256:" + new string('9', 64);
                break;
            case "invalid-case-id":
                payload["case_id"] = "active-frozen/" + new string('9', 64);
                break;
            default:
                throw new ArgumentOutOfRangeException(nameof(violation), violation, "unknown fixture violation");
        }

        var payloadElement = JsonSerializer.SerializeToElement(payload);
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent("Freeze", payloadElement);
        var identity = FrozenLedgerCanonicalWriter.EventIdentity(encoded.Hash);
        var newPath = FrozenLedgerChangeClassifier.AcceptedPath(identity);
        fixture.Files.Remove(oldPath);
        fixture.Files[newPath] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
    }

    private static AdmissionOutcome CheckProductionFreezeFixture(
        string repositoryRoot,
        TemporaryDirectory reports,
        ProductionFreezeFixture fixture)
    {
        var environment = new ProductionCliEnvironment(
            repositoryRoot,
            new GitRepositoryGateway(repositoryRoot),
            new FakeLeanReportSource(null));
        return environment.Check(
        [
            "--protected-base", fixture.ProtectedBase,
            "--candidate-lean-report", WriteCandidateReport(reports, fixture.RuleFixture),
        ]);
    }

    private static Diagnostic AssertFrozenAnchorRejection(AdmissionOutcome outcome)
    {
        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostics = rejected.Diagnostics
            .Where(static item => item.RuleId == RuleId.CreateKnown(8))
            .ToArray();
        Assert.NotEmpty(diagnostics);
        Assert.All(
            rejected.Diagnostics,
            static item => Assert.Equal(RuleId.CreateKnown(8), item.RuleId));
        return diagnostics[0];
    }

    private static int GitExitCode(string root, params string[] arguments)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = root,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in arguments)
        {
            startInfo.ArgumentList.Add(argument);
        }

        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("git did not start");
        _ = process.StandardOutput.ReadToEnd();
        _ = process.StandardError.ReadToEnd();
        process.WaitForExit();
        return process.ExitCode;
    }

    private static string TagGitOid(string oid) =>
        (oid.Length == 40 ? "git-sha1:" : "git-sha256:") + oid;

    private static string RenderOutcome(AdmissionOutcome outcome) => outcome switch
    {
        AdmissionOutcome.RuleRejected rejected => string.Join(
            '\n',
            rejected.Diagnostics.Select(static diagnostic => diagnostic.Render())),
        AdmissionOutcome.InfrastructureFailure failure => failure.Message,
        _ => outcome.ToString() ?? outcome.GetType().Name,
    };

    private sealed record ProductionFreezeFixture(
        RuleFixture RuleFixture,
        string ProtectedBase,
        string AnchorCommit);
}
