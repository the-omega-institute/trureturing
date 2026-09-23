using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void ConfigurationTestsRunWithoutCliTestExecution(string mode)
    {
        var plan = Plan("tools/tests/StrataLint.Configuration.Tests/RegistryTests.cs", "", mode);
        Assert.Equal(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.Configuration.Tests/StrataLint.Configuration.Tests.csproj",
        }, Strings(plan["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void HeaderScriptRunsOnlyItsCompleteScriptProject(string mode)
    {
        var plan = Plan("tools/scripts/agent/header-check.sh", "", mode);
        Assert.Equal(new[] {
            "tools/tests/StrataLint.HeaderScript.Tests/StrataLint.HeaderScript.Tests.csproj",
        }, Strings(plan["execution"]!["tests"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        if (mode == "push") Assert.DoesNotContain("elan", Strings(plan["cache_layers"]!));
    }

    [Theory]
    [InlineData("Meta/domains.yaml")]
    [InlineData("tools/scripts/agent/header-check.sh")]
    [InlineData("tools/StrataLint.Configuration/RegistryLoader.cs")]
    [InlineData("tools/tests/StrataLint.Tests/Commands/Playbook/DepositHeaderWorkflowScriptTests.cs")]
    public void NonCacheInputsDoNotSelectCacheTests(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan(path, "", mode);
            Assert.DoesNotContain(Strings(plan["execution"]!["tests"]!),
                test => test.Contains("StrataLint.Cache.", StringComparison.Ordinal));
        }
    }
    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void ReleaseCacheFixtureSelectsItsCompleteProjectAndMakeDependency(string mode)
    {
        var plan = Plan("tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py", "", mode);
        Assert.Equal(new[] {
            "tools/tests/StrataLint.Cache.Release.Tests/StrataLint.Cache.Release.Tests.csproj",
        }, Strings(plan["execution"]!["tests"]!));
        Assert.Contains("make", Strings(plan["tools"]!));
        if (mode == "push") Assert.DoesNotContain("lake", Strings(plan["tools"]!));
    }
}
