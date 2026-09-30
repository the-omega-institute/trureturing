using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void LeanCacheAdapterInputSelectsItsCompleteConsumer(string mode)
    {
        var plan = Plan("tools/scripts/worktree/lean-cache-run.sh", "", mode, "M");
        Assert.Equal(OrderedConsumers(new[]
        {
            "StrataLint.ArchitectureTests",
            "StrataLint.CoverBatch.Tests",
            "StrataLint.Lean.Tests",
            "StrataLint.NativeTransportIntegration.Tests",
            "StrataLint.RepositoryConfiguration.Tests",
            "StrataLint.RepositoryContract.Tests",
            "StrataLint.RepositoryFileMap.Tests",
            "StrataLint.RepositoryTopology.Tests",
            "StrataLint.Scribe.Tests",
            "StrataLint.Tests",
        }.Select(name => $"tools/tests/{name}/{name}.csproj")),
            Strings(plan["execution"]!["tests"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
    }

}
