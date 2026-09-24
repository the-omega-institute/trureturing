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
                "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
                RepositoryTopologyProject,
                "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            }), Strings(Plan($"tools/TestSupport/StrataLint.CoverTestSupport/{file}", "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void ValuesKernelBytesSelectCoverBatchEvenWhenFixtureOverwritesThem(string mode)
    {
        var plan = Plan("Golden/values-kernels.toml", "", mode);
        Assert.Equal(WithWorktreeContract(new[] { CoverBatchProject }), Strings(plan["execution"]!["tests"]!));
        Assert.Equal(new[] { "current", "delta", "filemap", "scribe", "test-cover-batch", "test-worktree-contract" },
            Strings(plan["declared_require"]!));
    }

    [Theory]
    [InlineData("D5/S3/Constants/Values.lean")]
    [InlineData("D5/X_Frontier/ValuesProducer.lean")]
    [InlineData("Meta/Digestion/backfill/admission-resource-probe.json")]
    [InlineData("docs/reports/prime-slab-corner-order-0909.json")]
    public void CoverBatchRuntimeReadsDoNotExpandContentOrNoResourcePolicy(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(path.StartsWith("D5/", StringComparison.Ordinal)
                    ? new[] { InstructionContractProject, RepositoryDigestionProject }
                    : path.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal)
                        ? new[] { RepositoryDigestionProject } : []),
                Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }
}
