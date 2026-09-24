using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string RepositoryFileMapProject =
        "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj";

    [Theory]
    [InlineData("push", "M")]
    [InlineData("pr", "M")]
    [InlineData("push", "D")]
    [InlineData("pr", "D")]
    [InlineData("push", "R")]
    [InlineData("pr", "R")]
    public void RegistryReferencedFilesSelectTheirCompletePresenceConsumer(string mode, string change)
    {
        foreach (var path in new[]
        {
            "CLAUDE.md",
            "LICENSE",
            "README.md",
            "Trureturing.lean",
            "D5/X_Frontier/HeartsAuthorizations.md",
        })
        {
            var plan = Plan(path, "", mode, change);
            Assert.Contains(RepositoryFileMapProject, Strings(plan["execution"]!["tests"]!));
            Assert.Contains("test-repository-filemap", Strings(plan["stages"]!["engineering"]!["resources"]!));
            Assert.Equal("required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
            Assert.DoesNotContain("test-cache", Strings(plan["resources"]!));
            if (path is "LICENSE" or "README.md" or "Trureturing.lean")
                Assert.Equal(WithWorktreeContract(new[] { RepositoryFileMapProject }), Strings(plan["execution"]!["tests"]!));
        }
    }
}
