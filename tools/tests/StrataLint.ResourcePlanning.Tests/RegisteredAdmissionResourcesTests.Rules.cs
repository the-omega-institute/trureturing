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
        Assert.Equal(WithRepositoryContract(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.Rules.Tests/StrataLint.Rules.Tests.csproj",
        }), Strings(plan["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void ValuesProjectionSelectsRuleBehaviorTests(string mode)
    {
        var plan = Plan("Evidence/D5/values.json", "", mode);
        Assert.Equal(WithRepositoryContract(new[] {
            "tools/tests/StrataLint.Rules.Tests/StrataLint.Rules.Tests.csproj",
        }), Strings(plan["execution"]!["tests"]!));
    }
}
