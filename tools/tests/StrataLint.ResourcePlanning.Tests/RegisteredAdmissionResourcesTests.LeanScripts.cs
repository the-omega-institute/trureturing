using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("StrataLint.LeanReportScript.Tests", "LeanReportInputScriptTests.cs", "push")]
    [InlineData("StrataLint.LeanReportScript.Tests", "LeanReportInputScriptTests.cs", "pr")]
    [InlineData("StrataLint.ResourceObservation.Tests", "ResourceObservationLibraryTests.cs", "push")]
    [InlineData("StrataLint.ResourceObservation.Tests", "ResourceObservationLibraryTests.cs", "pr")]
    public void ReportAndObservationTestsSelectTheirCompleteConsumerProject(string project, string file, string mode)
    {
        var plan = Plan($"tools/tests/{project}/{file}", "", mode);
        Assert.Equal(WithRepositoryContract(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
            $"tools/tests/{project}/{project}.csproj",
            RepositoryTopologyProject,
        }), Strings(plan["execution"]!["tests"]!));
    }
}
