using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class ResourceAdapterTests
{
    [Theory]
    [InlineData("multi-commit")]
    [InlineData("non-ancestor")]
    [InlineData("initial")]
    [InlineData("available")]
    [InlineData("unavailable")]
    [InlineData("mismatched-after")]
    [InlineData("reusable")]
    public void CheckoutObtainsOnlyFixedPushEndpointsBeforeRemovingRemotes(string scenario)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var before = fixture.Commit;
        if (scenario == "non-ancestor")
        {
            var tree = SharedBuildContractTests.Git(fixture.Root, "rev-parse", before + "^{tree}");
            before = SharedBuildContractTests.Git(fixture.Root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "commit-tree", tree, "-m", "independent event endpoint");
            SharedBuildContractTests.Git(fixture.Root, "update-ref", "refs/heads/retained-before", before);
        }
        fixture.Write("docs/early.md", "first commit in push\n");
        fixture.CommitPlan();
        fixture.Write("docs/later.md", "second commit in push\n");
        fixture.CommitPlan();
        if (scenario == "initial") before = new string('0', 40);
        if (scenario == "unavailable") before = new string('f', 40);
        if (scenario == "available") before = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^1");
        var root = Path.Combine(fixture.Root, "build/shallow-checkout");
        SharedBuildContractTests.Git(fixture.Root, "clone", "--no-local", "--no-tags", "--depth=2",
            new Uri(fixture.Root + Path.DirectorySeparatorChar).AbsoluteUri, root);
        Assert.Equal(fixture.Commit, SharedBuildContractTests.Git(root, "rev-parse", "HEAD"));
        Assert.Equal("true", SharedBuildContractTests.Git(root, "rev-parse", "--is-shallow-repository"));
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, before, scenario == "mismatched-after" ? before : fixture.Commit);
        environment["CI_PUSH_BEFORE"] = "";
        environment["CI_PUSH_AFTER"] = "";
        environment["CANDIDATE_SHA"] = fixture.Commit;
        if (scenario == "reusable")
        {
            environment["CI_WORKFLOW_INPUTS"] = new JsonObject { ["candidate_sha"] = fixture.Commit }.ToJsonString();
            environment["GITHUB_EVENT_PATH"] = Path.Combine(fixture.Root, "build/absent-event.json");
        }
        var command = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow/ci.py");
        var result = SharedBuildContractTests.Process(root, "python3", ["-B", command, "checkout", "--repository", root,
            "--commit", fixture.Commit], environment, TestBudgets.WorkflowProcessHangGuard);
        if (scenario is "unavailable" or "mismatched-after")
        {
            Assert.Equal(2, result.Exit);
            Assert.Contains(scenario == "unavailable" ? "PUSH_BEFORE_UNAVAILABLE" : "push event after does not match", result.Text, StringComparison.Ordinal);
            Assert.False(File.Exists(Path.Combine(root, "build/ci/plan.json")));
            return;
        }
        Assert.True(result.Exit == 0, result.Text);
        Assert.Empty(SharedBuildContractTests.Git(root, "remote"));
        Assert.Empty(SharedBuildContractTests.Git(root, "for-each-ref", "--format=%(refname)", "refs/remotes/"));
        Assert.Equal(fixture.Commit, SharedBuildContractTests.Git(root, "rev-parse", "HEAD"));
        Assert.Equal("true", SharedBuildContractTests.Git(root, "rev-parse", "--is-shallow-repository"));
        if (scenario == "reusable") return;
        if (scenario is "multi-commit" or "non-ancestor")
        {
            Assert.Equal("commit", SharedBuildContractTests.Git(root, "cat-file", "-t", before));
            Assert.Equal("2", SharedBuildContractTests.Git(root, "rev-list", "--count", "HEAD"));
        }
        var plan = Path.Combine(root, "build/ci/plan.json");
        var changes = Path.Combine(root, "build/ci/changes.json");
        environment["CI_PLAN_PATH"] = plan;
        environment["CI_CHANGES_PATH"] = changes;
        var planned = SharedBuildContractTests.Process(root, "python3", ["-B", command, "push-plan", "--repository", root,
            "--commit", fixture.Commit], environment, TestBudgets.WorkflowProcessHangGuard);
        Assert.True(planned.Exit == 0, planned.Text);
        var scope = JsonNode.Parse(File.ReadAllText(changes))!;
        Assert.True(scope["complete"]!.GetValue<bool>());
        Assert.Equal(before, scope["origin"]!["before"]!.ToString());
        var paths = scope["changes"]!.AsArray().Select(row => row!["new"]!["path"]!.ToString()).ToArray();
        Assert.Contains("docs/later.md", paths);
        if (scenario is "multi-commit" or "non-ancestor") Assert.Contains("docs/early.md", paths);
        if (scenario == "available") Assert.DoesNotContain("docs/early.md", paths);
        Assert.Equal("not-applicable", JsonNode.Parse(File.ReadAllText(plan))!["stages"]!["delta"]!["status"]!.ToString());
    }
}
