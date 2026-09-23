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
            Assert.Equal(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                CoverBatchProject,
                RepositoryTopologyProject,
            }, Strings(Plan($"tools/tests/StrataLint.CoverBatch.Tests/{file}", "", mode)["execution"]!["tests"]!));
    }

    [Fact]
    public void CoverBatchLockSelectsItsCompleteProject()
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(new[] { CoverBatchProject },
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
            Assert.Equal(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                CoverBatchProject,
                RepositoryTopologyProject,
                "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            }, Strings(Plan($"tools/TestSupport/StrataLint.CoverTestSupport/{file}", "", mode)["execution"]!["tests"]!));
    }
}
