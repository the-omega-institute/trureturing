using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string RepositoryContractProject =
        "tools/tests/StrataLint.RepositoryContract.Tests/StrataLint.RepositoryContract.Tests.csproj";

    [Theory]
    [InlineData("CliVerbLinkageTests.cs", true)]
    [InlineData("StrataLint.RepositoryContract.Tests.csproj", true)]
    [InlineData("packages.lock.json", false)]
    public void RepositoryContractChangesSelectOnlyTheirCompleteProjectAndArchitecture(string file, bool architecture)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan("tools/tests/StrataLint.RepositoryContract.Tests/" + file, "", mode);
            Assert.Equal(WithRepositoryContract(architecture
                    ? new[] { "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj" } : []),
                Strings(plan["execution"]!["tests"]!));
            Assert.Equal(WithRepositoryContract(new[] { architecture
                    ? "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj"
                    : "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" }),
                Strings(plan["execution"]!["projects"]!));
            Assert.DoesNotContain("test-cli", Strings(plan["resources"]!));
        }
    }

    [Theory]
    [InlineData("tools/scripts/agent/merge-gate.sh", "StrataLint.ArchitectureTests", "StrataLint.Tests")]
    [InlineData("tools/tests/StrataLint.Configuration.Tests/RegistryTests.cs", "StrataLint.ArchitectureTests", "StrataLint.Configuration.Tests")]
    [InlineData("tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py", "StrataLint.Cache.Release.Tests", null)]
    public void ExistingEngineeringPathsSelectRepositoryContract(string path, string first, string? second)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var consumers = new[] { first }.Concat(second is null ? [] : new[] { second });
            Assert.Equal(WithRepositoryContract(consumers.Select(name => $"tools/tests/{name}/{name}.csproj")),
                Strings(Plan(path, "", mode)["execution"]!["tests"]!));
        }
    }

    [Theory]
    [InlineData("README.md")]
    [InlineData("tools/lean-inspector/README.md")]
    [InlineData("docs/develop/theory/RepositoryContractProbe.md")]
    [InlineData("docs/reports/prime-slab-corner-order-0909.json")]
    [InlineData("tools/scripts/agent/openproblem/templates/review-template.md")]
    [InlineData("D5/F/NumberTheory/AdmissionResourceProbe.lean")]
    [InlineData("Meta/Digestion/backfill/admission-resource-probe.json")]
    public void ContentAndMetadataPathsDoNotAcquireEngineeringTests(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan(path, "", mode);
            Assert.Empty(Strings(plan["execution"]!["tests"]!));
            Assert.Equal("not-required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            Assert.DoesNotContain("test-repository-contract", Strings(plan["resources"]!));
        }
    }

    private static IEnumerable<string> WithRepositoryContract(IEnumerable<string> consumers) =>
        consumers.Append(RepositoryContractProject).Order(StringComparer.Ordinal);
}
