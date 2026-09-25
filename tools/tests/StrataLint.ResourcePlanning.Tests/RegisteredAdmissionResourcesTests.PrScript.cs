using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void PrToolChangesRunOnlyTheirCompleteScriptProject(string mode)
    {
        var plan = Plan("tools/scripts/pr.sh", "", mode);
        Assert.Equal(WithRepositoryContract(new[] {
            "tools/tests/StrataLint.PrScript.Tests/StrataLint.PrScript.Tests.csproj",
        }), Strings(plan["execution"]!["tests"]!));
    }
}
