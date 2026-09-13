using System.Text.Json.Nodes;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class ResourceExecutionPlanTests
{
    [Fact]
    public void ForgedCandidateIsRejectedBeforeStageExecution()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        var plan = JsonNode.Parse(File.ReadAllText(fixture.Plan))!;
        plan["candidate"]!["commit"] = new string('a', 40);
        File.WriteAllText(fixture.Plan, plan.ToJsonString());
        Assert.Throws<InvalidDataException>(() => ResourceExecutionPlan.Load(fixture.Root, fixture.Plan, fixture.Changes));
    }

    [Fact]
    public void ResourceSubsetMustContainRegisteredPrerequisites()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        var plan = JsonNode.Parse(File.ReadAllText(fixture.Plan))!;
        plan["resources"] = new JsonArray("filemap");
        plan["stages"]!["build"]!["resources"] = new JsonArray();
        plan["stages"]!["build"]!["status"] = "not-required";
        File.WriteAllText(fixture.Plan, plan.ToJsonString());
        Assert.Throws<InvalidDataException>(() => ResourceExecutionPlan.Load(fixture.Root, fixture.Plan, fixture.Changes));
    }
}
