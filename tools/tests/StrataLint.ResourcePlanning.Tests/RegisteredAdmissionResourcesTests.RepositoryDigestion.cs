using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string RepositoryDigestionProject =
        "tools/tests/StrataLint.RepositoryDigestion.Tests/StrataLint.RepositoryDigestion.Tests.csproj";

    [Theory]
    [InlineData("push", "M")]
    [InlineData("pr", "M")]
    [InlineData("push", "D")]
    [InlineData("pr", "D")]
    [InlineData("push", "R")]
    [InlineData("pr", "R")]
    public void RepositoryDigestionInputsSelectTheirCompleteConsumer(string mode, string change)
    {
        foreach (var path in new[]
        {
            "D5/X_Frontier/Hearts.lean",
            "Meta/Digestion/backfill/pzg-v170/source.toml",
            "Meta/Digestion/backfill/pzg-v170/residual-open/8eb0bfb6d9c7aa1dc7ddd5faa46452907d7d4aa8efc4b52574393bb91aeed22d.yaml",
        })
        {
            var plan = Plan(path, "", mode, change);
            Assert.Equal(WithWorktreeContract(path.StartsWith("D5/", StringComparison.Ordinal)
                    ? new[] { InstructionContractProject, RepositoryDigestionProject }
                    : new[] { RepositoryDigestionProject, SourceAtomizerProject }),
                Strings(plan["execution"]!["tests"]!));
            Assert.Contains("test-repository-digestion", Strings(plan["stages"]!["engineering"]!["resources"]!));
            Assert.Equal("required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        }
    }
}
