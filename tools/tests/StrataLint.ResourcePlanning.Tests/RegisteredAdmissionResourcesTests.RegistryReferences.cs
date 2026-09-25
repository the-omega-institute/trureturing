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
            var readsBody = path == "Trureturing.lean";
            var structural = change is "D" or "R";
            Assert.Equal(readsBody || structural,
                Strings(plan["execution"]!["tests"]!).Contains(RepositoryFileMapProject));
            Assert.Equal(readsBody || structural,
                Strings(plan["stages"]!["engineering"]!["resources"]!).Contains("test-repository-filemap"));
            Assert.Equal(structural, Strings(plan["execution"]!["tests"]!).Contains(RepositoryTopologyProject));
            Assert.Equal(readsBody || structural || path == "CLAUDE.md" || path.StartsWith("D5/", StringComparison.Ordinal)
                ? "required" : "not-required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
            Assert.DoesNotContain("test-cache", Strings(plan["resources"]!));
            if (path is "LICENSE" or "README.md" or "Trureturing.lean")
                Assert.Equal(WithPathInventory(readsBody ? new[] { RepositoryFileMapProject, WorktreeContractProject } : [], change), Strings(plan["execution"]!["tests"]!));
        }
    }
}
