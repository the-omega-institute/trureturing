using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void FileMapPolicyTestsRunTheirCompleteProjectWithoutCliTests(string mode)
    {
        var plan = Plan("tools/tests/StrataLint.FileMap.Tests/FileMapPolicyTests.cs", "", mode);
        Assert.Equal(WithRepositoryContract(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.FileMap.Tests/StrataLint.FileMap.Tests.csproj",
            "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
            RepositoryTopologyProject,
        }), Strings(plan["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void FileMapPolicyImplementationRetainsItsPolicyAndCommandConsumers(string mode)
    {
        var plan = Plan("tools/StrataLint.FileMap/FileMapPolicy.cs", "", mode);
        Assert.Equal(WithRepositoryContract(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.CliIntegration.Tests/StrataLint.CliIntegration.Tests.csproj",
            "tools/tests/StrataLint.FileMap.Tests/StrataLint.FileMap.Tests.csproj",
            "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            RepositoryTopologyProject,
            SourceAtomizerProject,
        }), Strings(plan["execution"]!["tests"]!));
    }
}
