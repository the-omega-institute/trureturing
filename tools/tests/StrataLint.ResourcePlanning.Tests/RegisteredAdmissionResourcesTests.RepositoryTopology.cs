using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string RepositoryTopologyProject =
        "tools/tests/StrataLint.RepositoryTopology.Tests/StrataLint.RepositoryTopology.Tests.csproj";

    [Theory]
    [InlineData("ProductionEnvironmentTests.cs")]
    [InlineData("DotnetTestScriptTests.cs")]
    [InlineData("StrataLint.RepositoryTopology.Tests.csproj")]
    public void RepositoryTopologySourcesSelectTheirCompleteProject(string file)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan($"tools/tests/StrataLint.RepositoryTopology.Tests/{file}", "", mode);
            Assert.Equal(WithRepositoryContract(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                RepositoryTopologyProject,
            }), Strings(plan["execution"]!["tests"]!));
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        }
    }

    [Fact]
    public void RepositoryTopologyLockSelectsItsCompleteProject()
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithRepositoryContract(new[] { RepositoryTopologyProject }),
                Strings(Plan("tools/tests/StrataLint.RepositoryTopology.Tests/packages.lock.json", "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/scripts/pr.sh")]
    [InlineData("tools/scripts/report/report-supervisor.sh")]
    [InlineData("tools/scripts/worktree/lean-cache-run.sh")]
    [InlineData("tools/scripts/agent/openproblem/README.md")]
    [InlineData("D5/F/NumberTheory/AdmissionResourceProbe.lean")]
    [InlineData("Meta/Digestion/backfill/admission-resource-probe.json")]
    [InlineData("docs/reports/prime-slab-corner-order-0909.json")]
    public void RepositoryTopologyDoesNotTurnIndexMetadataIntoUnrelatedExecution(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.DoesNotContain(RepositoryTopologyProject,
                Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/scripts/dotnet-test.sh", "StrataLint.ArchitectureTests,StrataLint.RepositoryTopology.Tests,StrataLint.Tests,StrataLint.WorkflowScript.Tests")]
    [InlineData("tools/TestSupport/StrataLint.CliTestSupport/FakeRepositoryGateway.cs", "StrataLint.ArchitectureTests,StrataLint.CliIntegration.Tests,StrataLint.RepositoryTopology.Tests,StrataLint.Tests")]
    [InlineData("tools/TestSupport/StrataLint.CliTestSupport/FakeLeanReportSource.cs", "StrataLint.ArchitectureTests,StrataLint.CliIntegration.Tests,StrataLint.RepositoryTopology.Tests,StrataLint.Tests")]
    public void RepositoryTopologyRealInputsSelectTheirCompleteConsumers(string path, string consumers)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithRepositoryContract(consumers.Split(',').Select(name => $"tools/tests/{name}/{name}.csproj")),
                Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

}
