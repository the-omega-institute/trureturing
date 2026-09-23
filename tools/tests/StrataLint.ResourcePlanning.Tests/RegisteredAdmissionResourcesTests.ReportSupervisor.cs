using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void ReportSupervisorFixtureChangesSelectTheirCompleteProject(string mode)
    {
        var plan = Plan("tools/tests/StrataLint.ReportSupervisor.Tests/ReportSupervisorFixture.cs", "", mode);
        Assert.Equal(WithRepositoryContract(new[] {
            "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
            "tools/tests/StrataLint.ReportSupervisor.Tests/StrataLint.ReportSupervisor.Tests.csproj",
        }), Strings(plan["execution"]!["tests"]!));
    }
}
