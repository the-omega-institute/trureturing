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
            "tools/tests/StrataLint.Rules.Tests/StrataLint.Rules.Tests.csproj",
        }), Strings(plan["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void ValuesProjectionRetainsItsFileMapScribeAndWorktreeContractObligations(string mode)
    {
        var plan = Plan("Evidence/D5/values.json", "", mode);
        Assert.Equal(new[] { "filemap", "scribe", "test-worktree-contract" }, Strings(plan["declared_require"]!));
        Assert.Equal(WithWorktreeContract([]), Strings(plan["execution"]!["tests"]!));
        Assert.Equal(new[] { "build", "filemap", "lean", "lean-report", "scribe", "test-worktree-contract" }, Strings(plan["resources"]!));
        Assert.Equal(new[] { "filemap", "scribe-describe", "scribe-markdown", "scribe-projections" },
            Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap" }, Strings(plan["execution"]!["steps"]!));
        Assert.Equal("required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
    }
}
