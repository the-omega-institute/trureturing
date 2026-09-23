using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void LeanCacheAdapterInputSelectsItsCompleteConsumer(string mode)
    {
        var plan = Plan("tools/scripts/worktree/lean-cache-run.sh", "", mode);
        Assert.Equal(new[]
        {
            "StrataLint.ArchitectureTests",
            "StrataLint.Lean.Tests",
            "StrataLint.LeanCacheScript.Tests",
            "StrataLint.NativeTransportIntegration.Tests",
            "StrataLint.Tests",
        }.Select(name => $"tools/tests/{name}/{name}.csproj"),
            Strings(plan["execution"]!["tests"]!));
    }
}
