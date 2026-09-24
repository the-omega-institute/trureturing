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
        Assert.Equal(WithWorktreeContract(new[]
        {
            "StrataLint.ArchitectureTests",
            "StrataLint.CoverBatch.Tests",
            "StrataLint.Lean.Tests",
            "StrataLint.LeanCacheScript.Tests",
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

    [Theory]
    [InlineData("LeanCacheRunScriptTests.cs", true)]
    [InlineData("StrataLint.LeanCacheScript.Tests.csproj", true)]
    [InlineData("packages.lock.json", false)]
    public void LeanCacheAdapterTestInputsSelectOnlyTheirCompleteProject(string file, bool architecture)
    {
        var plan = Plan($"tools/tests/StrataLint.LeanCacheScript.Tests/{file}", "", "push");
        var expected = architecture
            ? new[] { "StrataLint.ArchitectureTests", "StrataLint.LeanCacheScript.Tests", "StrataLint.RepositoryFileMap.Tests", "StrataLint.RepositoryTopology.Tests" }
            : new[] { "StrataLint.LeanCacheScript.Tests" };
        Assert.Equal(WithWorktreeContract(expected.Select(name => $"tools/tests/{name}/{name}.csproj")),
            Strings(plan["execution"]!["tests"]!));
    }

}
