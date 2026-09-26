using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void RuleBehaviorChangesSelectTheirCompleteProject(string mode)
    {
        var plan = Plan("tools/tests/StrataLint.Rules.Tests/RuleEngineTests.cs", "", mode);
        Assert.Equal(WithWorktreeContract(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
            "tools/tests/StrataLint.Rules.Tests/StrataLint.Rules.Tests.csproj",
            RepositoryTopologyProject,
        }), Strings(plan["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void ValuesProjectionRetainsFileMapAndScribeWithoutEngineering(string mode)
    {
        var plan = Plan("Evidence/D5/values/k44352f53796e746865746963.value.json", "", mode);
        Assert.Equal(new[] { "filemap", "scribe" }, Strings(plan["declared_require"]!));
        Assert.Equal(Array.Empty<string>(), Strings(plan["execution"]!["tests"]!));
        Assert.Equal(new[] { "build", "filemap", "lean", "lean-report", "scribe" }, Strings(plan["resources"]!));
        Assert.Equal(new[] { "filemap", "scribe-describe", "scribe-markdown", "scribe-projections" },
            Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap" }, Strings(plan["execution"]!["steps"]!));
        Assert.Equal("not-required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
    }
}
