using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string RepositoryTopologyProject =
        "tools/tests/StrataLint.RepositoryTopology.Tests/StrataLint.RepositoryTopology.Tests.csproj";

    private static IEnumerable<string> WithPathInventory(IEnumerable<string> consumers, string change) =>
        WithWorktreeContract(consumers.Concat(change is "A" or "D" or "R"
            ? new[] { RepositoryFileMapProject, RepositoryTopologyProject } : []));

    [Theory]
    [InlineData("push", "A")]
    [InlineData("pr", "A")]
    [InlineData("push", "D")]
    [InlineData("pr", "D")]
    [InlineData("push", "R")]
    [InlineData("pr", "R")]
    public void RepositoryPathChangesRunBothCompleteInventoryConsumers(string mode, string change)
    {
        var plan = Plan("docs/reports/repository-inventory-probe.md", "", mode, change);
        Assert.Equal(WithWorktreeContract(new[] { RepositoryFileMapProject, RepositoryTopologyProject }),
            Strings(plan["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("ProductionEnvironmentTests.cs")]
    [InlineData("DotnetTestScriptTests.cs")]
    [InlineData("StrataLint.RepositoryTopology.Tests.csproj")]
    public void RepositoryTopologySourcesSelectTheirCompleteProject(string file)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan($"tools/tests/StrataLint.RepositoryTopology.Tests/{file}", "", mode);
            Assert.Equal(WithWorktreeContract(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                RepositoryTopologyProject,
            }.Concat(file.EndsWith(".cs", StringComparison.Ordinal) ? new[] { RepositoryFileMapProject } : [])),
                Strings(plan["execution"]!["tests"]!));
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        }
    }

    [Fact]
    public void RepositoryTopologyLockSelectsItsCompleteProject()
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(new[] { RepositoryTopologyProject }),
                Strings(Plan("tools/tests/StrataLint.RepositoryTopology.Tests/packages.lock.json", "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/scripts/pr.sh")]
    [InlineData("tools/scripts/report/report-supervisor.sh")]
    [InlineData("tools/scripts/agent/openproblem/README.md")]
    [InlineData("D5/S0/NumberTheory/AdmissionResourceProbe.lean")]
    [InlineData("Meta/Digestion/backfill/admission-resource-probe.json")]
    [InlineData("docs/reports/prime-slab-corner-order-0909.json")]
    public void RepositoryTopologyDoesNotTurnIndexMetadataIntoUnrelatedExecution(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.DoesNotContain(RepositoryTopologyProject,
                Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/scripts/dotnet-test.sh", "StrataLint.ArchitectureTests,StrataLint.RepositoryContract.Tests,StrataLint.RepositoryTopology.Tests,StrataLint.WorkflowScript.Tests")]
    [InlineData("tools/TestSupport/StrataLint.CliTestSupport/FakeRepositoryGateway.cs", "StrataLint.ArchitectureTests,StrataLint.CliIntegration.Tests,StrataLint.CoverBatch.Tests,StrataLint.RepositoryFileMap.Tests,StrataLint.RepositoryTopology.Tests,StrataLint.SourceAtomizer.Tests,StrataLint.Tests,StrataLint.TruthRelease.Tests")]
    [InlineData("tools/TestSupport/StrataLint.CliTestSupport/FakeLeanReportSource.cs", "StrataLint.ArchitectureTests,StrataLint.CliIntegration.Tests,StrataLint.CoverBatch.Tests,StrataLint.RepositoryFileMap.Tests,StrataLint.RepositoryTopology.Tests,StrataLint.SourceAtomizer.Tests,StrataLint.Tests,StrataLint.TruthRelease.Tests")]
    public void RepositoryTopologyRealInputsSelectTheirCompleteConsumers(string path, string consumers)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(consumers.Split(',').Select(name => $"tools/tests/{name}/{name}.csproj")),
                Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

}
