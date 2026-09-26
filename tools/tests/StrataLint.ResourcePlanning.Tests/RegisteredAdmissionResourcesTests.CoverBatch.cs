using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string CoverBatchProject =
        "tools/tests/StrataLint.CoverBatch.Tests/StrataLint.CoverBatch.Tests.csproj";

    [Theory]
    [InlineData("CoverBatchCommandTests.cs")]
    [InlineData("CoverBatchCommandTests.Emission.cs")]
    [InlineData("CoverBatchCommandTests.Loads.cs")]
    [InlineData("CoverBatchCommandTests.Scribe.cs")]
    [InlineData("AssemblyInfo.cs")]
    [InlineData("Usings.cs")]
    [InlineData("StrataLint.CoverBatch.Tests.csproj")]
    public void CoverBatchSourcesSelectTheirCompleteProject(string file)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                CoverBatchProject,
                RepositoryTopologyProject,
            }.Concat(file.EndsWith(".cs", StringComparison.Ordinal)
                ? new[] { "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj" } : [])), Strings(Plan($"tools/tests/StrataLint.CoverBatch.Tests/{file}", "", mode)["execution"]!["tests"]!));
    }

    [Fact]
    public void CoverBatchLockSelectsItsCompleteProject()
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(new[] { CoverBatchProject }),
                Strings(Plan("tools/tests/StrataLint.CoverBatch.Tests/packages.lock.json", "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("CoverAtomFixtures.cs")]
    [InlineData("CoverWorld.LedgerFixture.cs")]
    [InlineData("CoverSpec.ReceiptBinding.cs")]
    [InlineData("StrataLint.CoverTestSupport.csproj")]
    [InlineData("packages.lock.json")]
    public void CoverSupportSelectsItsConsumersAndRepositoryAudits(string file)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                CoverBatchProject,
                RepositoryTopologyProject,
                "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            }.Concat(file.EndsWith(".cs", StringComparison.Ordinal) ? new[] { RepositoryFileMapProject } : [])),
                Strings(Plan($"tools/TestSupport/StrataLint.CoverTestSupport/{file}", "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void ValuesKernelBytesSelectCoverBatchEvenWhenFixtureOverwritesThem(string mode)
    {
        var plan = Plan("Golden/values-kernels.toml", "", mode);
        Assert.Equal(OrderedConsumers(new[] { CoverBatchProject, RepositoryFileMapProject }), Strings(plan["execution"]!["tests"]!));
        Assert.Equal(new[] { "current", "delta", "filemap", "scribe", "test-cover-batch", "test-repository-filemap" },
            Strings(plan["declared_require"]!));
    }

    [Theory]
    [InlineData("push", "M")]
    [InlineData("pr", "M")]
    [InlineData("push", "D")]
    [InlineData("pr", "D")]
    [InlineData("push", "R")]
    [InlineData("pr", "R")]
    public void CoverBatchLeanInputChangesSelectItsCompleteProject(string mode, string change)
    {
        foreach (var path in new[] { "D5/S3/Constants/Values.lean", "D5/X_Frontier/ValuesProducer.lean" })
        {
            var plan = Plan(path, "", mode, change);
            Assert.Equal(WithPathInventory(new[] { CoverBatchProject, InstructionContractProject, RepositoryDigestionProject, RepositoryFileMapProject, WorktreeContractProject }, change), Strings(plan["execution"]!["tests"]!));
            Assert.Equal(new[] { "test-cover-batch", "test-instruction-contract", "test-repository-digestion", "test-repository-filemap", "test-worktree-contract" }
                    .Concat(change is "D" or "R" ? new[] { "test-repository-topology" } : []).Order(StringComparer.Ordinal),
                Strings(plan["stages"]!["engineering"]!["resources"]!));
            Assert.Equal("required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            var input = Assert.Single(plan["paths"]!.AsArray(), row => row!["path"]!.GetValue<string>() == path);
            Assert.Contains("test-cover-batch", Strings(input!["require"]!));
            if (change == "R")
            {
                var destination = Assert.Single(plan["paths"]!.AsArray(),
                    row => row!["path"]!.GetValue<string>() == "docs/reports/instruction-contract-renamed.md");
                Assert.Equal(new[] { "test-repository-filemap", "test-repository-topology" }, Strings(destination!["require"]!));
            }
        }
    }

    [Theory]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Syntax.lean", true)]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Projection/OutputOnlyAudit.lean", true)]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Registry/Entries.lean", false)]
    public void InspectorSourceConsumersSelectOnlyTheirCompleteProjects(string path, bool grammarConsumer)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                CoverBatchProject,
                RepositoryFileMapProject,
            }.Concat(grammarConsumer
                ? new[] { "tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj" } : [])),
                Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("Meta/Digestion/backfill/admission-resource-probe.json")]
    [InlineData("docs/reports/prime-slab-corner-order-0909.json")]
    public void UnrelatedMetadataAndReportsDoNotSelectCoverBatch(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(OrderedConsumers(path.StartsWith("D5/", StringComparison.Ordinal)
                    ? new[] { InstructionContractProject, RepositoryDigestionProject, RepositoryFileMapProject }
                    : path.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal)
                        ? new[] { RepositoryDigestionProject, RepositoryFileMapProject } : [RepositoryFileMapProject]),
                Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }
}
