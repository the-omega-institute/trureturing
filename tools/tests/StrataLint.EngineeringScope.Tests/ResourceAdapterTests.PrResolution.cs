using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class ResourceAdapterTests
{
    [Theory]
    [InlineData("missing")]
    [InlineData("empty")]
    [InlineData("symbolic")]
    [InlineData("short")]
    [InlineData("nonhex")]
    [InlineData("zero")]
    [InlineData("newline")]
    public void PullRequestResolverRejectsInvalidEventIdentity(string defect)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        fixture.PrPlan();
        var value = defect switch
        {
            "symbolic" => "HEAD",
            "short" => new string('a', 39),
            "nonhex" => new string('g', 40),
            "zero" => new string('0', 40),
            "newline" => fixture.Commit + "\n",
            _ => "",
        };
        var head = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^2");
        var result = ResolvePullRequest(fixture, head, value, unsetEvent: defect == "missing");
        AssertUnpublishedResolution(fixture, result,
            "pull request event GITHUB_SHA must be a nonzero immutable 40-hex commit");
    }

    [Fact]
    public void PullRequestResolverRejectsMovedMergeCheckoutWithSameTriggeringHead()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        fixture.PrPlan();
        var (basis, head, moved) = MovePullRequestMerge(fixture);
        SharedBuildContractTests.Git(fixture.Root, "reset", "--hard", "refs/pull/17/merge");
        SharedBuildContractTests.Git(fixture.Root, "remote", "add", "origin", Path.Combine(fixture.Root, "unused-origin.git"));
        SharedBuildContractTests.Git(fixture.Root, "update-ref", "refs/remotes/origin/dev", basis);

        var result = ResolvePullRequest(fixture, head, fixture.Commit);
        AssertUnpublishedResolution(fixture, result, "checkout does not match pull request event GITHUB_SHA");
        Assert.Equal(moved, SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD"));
        Assert.Equal("origin", SharedBuildContractTests.Git(fixture.Root, "remote"));
        Assert.Equal(basis, SharedBuildContractTests.Git(fixture.Root, "rev-parse", "refs/remotes/origin/dev"));
    }

    [Fact]
    public void PullRequestResolverKeepsEventMergeWhenMergeRefMoves()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        fixture.PrPlan();
        var (basis, head, _) = MovePullRequestMerge(fixture);

        var result = ResolvePullRequest(fixture, head, fixture.Commit);
        Assert.True(result.Exit == 0, result.Text);
        var lines = File.ReadAllLines(Path.Combine(fixture.Root, "build/adapter-output"));
        Assert.All(lines.Where(line => line.StartsWith("candidate_sha=", StringComparison.Ordinal)),
            line => Assert.Equal("candidate_sha=" + fixture.Commit, line));
        Assert.Contains("base_sha=" + basis, lines);
        foreach (var name in new[] { "plan", "changes" })
        {
            var material = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/" + name + ".json")))!;
            Assert.Equal(fixture.Commit, material["candidate"]!["commit"]!.ToString());
            Assert.Equal(basis, material["base"]!.ToString());
            Assert.Equal(head, material["head"]!.ToString());
        }
    }

    [Fact]
    public void PullRequestResolverStillRejectsDifferentTriggeringHead()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        fixture.PrPlan();
        var wrongHead = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^1");
        var result = ResolvePullRequest(fixture, wrongHead, fixture.Commit);
        AssertUnpublishedResolution(fixture, result, "does not contain the triggering PR head");
    }

    private static (string Basis, string Head, string Moved) MovePullRequestMerge(ResourceRouteTests.ResourceFixture fixture)
    {
        string Git(params string[] arguments) => SharedBuildContractTests.Git(fixture.Root, arguments);
        string CommitTree(params string[] arguments) => Git(["-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit-tree", .. arguments]);
        var basis = Git("rev-parse", "HEAD^1");
        var head = Git("rev-parse", "HEAD^2");
        var tree = Git("rev-parse", "HEAD^{tree}");
        var nextBase = CommitTree(Git("rev-parse", basis + "^{tree}"), "-p", basis, "-m", "advanced base");
        var moved = CommitTree(tree, "-p", nextBase, "-p", head, "-m", "regenerated merge");
        Git("update-ref", "refs/pull/17/merge", moved);
        Assert.NotEqual(fixture.Commit, moved);
        Assert.Equal(head, Git("rev-parse", moved + "^2"));
        Assert.Equal(tree, Git("rev-parse", moved + "^{tree}"));
        return (basis, head, moved);
    }

    private static (int Exit, string Text) ResolvePullRequest(ResourceRouteTests.ResourceFixture fixture,
        string head, string eventCandidate, bool unsetEvent = false)
    {
        var environment = EnvironmentFor(fixture);
        environment["GITHUB_EVENT_NAME"] = "pull_request";
        environment["GITHUB_SHA"] = eventCandidate;
        return SharedBuildContractTests.Process(fixture.Root, "/usr/bin/env",
            [.. unsetEvent ? new[] { "-u", "GITHUB_SHA" } : [], "python3", "-B", "tools/scripts/workflow/ci.py",
                "resolve", "--repository", fixture.Root, "--head", head], environment, TestBudgets.WorkflowProcessHangGuard);
    }

    private static void AssertUnpublishedResolution(ResourceRouteTests.ResourceFixture fixture,
        (int Exit, string Text) result, string diagnostic)
    {
        Assert.Equal(2, result.Exit);
        Assert.Contains(diagnostic, result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("CI_WORKFLOW_IDENTITY", result.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/adapter-output")));
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/ci/plan.json")));
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/ci/changes.json")));
    }
}
