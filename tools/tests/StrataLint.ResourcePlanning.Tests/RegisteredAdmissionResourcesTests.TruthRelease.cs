using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string TruthReleaseProject =
        "tools/tests/StrataLint.TruthRelease.Tests/StrataLint.TruthRelease.Tests.csproj";

    [Theory]
    [InlineData("TruthReleaseCommandTests.cs")]
    [InlineData("AssemblyInfo.cs")]
    [InlineData("Usings.cs")]
    [InlineData("StrataLint.TruthRelease.Tests.csproj")]
    public void TruthReleaseSourcesSelectTheirCompleteProject(string file)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                RepositoryTopologyProject,
                TruthReleaseProject,
            }.Concat(file.EndsWith(".cs", StringComparison.Ordinal)
                ? new[] { "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj" } : [])),
                Strings(Plan($"tools/tests/StrataLint.TruthRelease.Tests/{file}", "", mode)["execution"]!["tests"]!));
    }

    [Fact]
    public void TruthReleaseLockSelectsItsCompleteProject()
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(new[] { TruthReleaseProject }),
                Strings(Plan("tools/tests/StrataLint.TruthRelease.Tests/packages.lock.json", "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("push", "M")]
    [InlineData("pr", "M")]
    [InlineData("push", "D")]
    [InlineData("pr", "D")]
    [InlineData("push", "R")]
    [InlineData("pr", "R")]
    public void TruthReleaseRuntimeChangesSelectAllActualConsumers(string mode, string change)
    {
        var inputs = new[]
        {
            (Path: "D5/S3/Midline/GoldenSpectralMarker.lean",
                Projects: new[] { CoverBatchProject, InstructionContractProject, RepositoryDigestionProject, TruthReleaseProject }),
            (Path: "Blueprint/D5/S3/Midline/GoldenSpectralMarker.md",
                Projects: new[] { TruthReleaseProject }),
            (Path: "Blueprint/D5/S3/Midline/GoldenSpectralMarker.scribe.cs",
                Projects: new[] { RepositoryContractProject,
                    "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
                    RepositoryTopologyProject, TruthReleaseProject }),
            (Path: "Golden/Projection/statement-projection-pilot-v1.json",
                Projects: new[] { "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
                    "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj", TruthReleaseProject }),
            (Path: "Golden/Projection/statement-projection-expansion-v1.json",
                Projects: new[] { "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
                    "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj", TruthReleaseProject }),
        };
        foreach (var (path, projects) in inputs)
        {
            var plan = Plan(path, "", mode, change);
            Assert.Equal(WithWorktreeContract(projects), Strings(plan["execution"]!["tests"]!));
            Assert.Equal("required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            var input = Assert.Single(plan["paths"]!.AsArray(), row => row!["path"]!.GetValue<string>() == path);
            Assert.Contains("test-truth-release", Strings(input!["require"]!));
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
            if (change == "R")
            {
                var destination = Assert.Single(plan["paths"]!.AsArray(),
                    row => row!["path"]!.GetValue<string>() == "docs/reports/instruction-contract-renamed.md");
                Assert.Equal(new[] { "test-worktree-contract" }, Strings(destination!["require"]!));
            }
        }
    }

    [Fact]
    public void SharedFrozenLedgerFixtureSelectsEveryRegisteredSupportConsumer()
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                "tools/tests/StrataLint.CliIntegration.Tests/StrataLint.CliIntegration.Tests.csproj",
                CoverBatchProject,
                "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
                RepositoryTopologyProject,
                SourceAtomizerProject,
                "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
                TruthReleaseProject,
            }), Strings(Plan("tools/TestSupport/StrataLint.CliTestSupport/FrozenLedgerTestData.cs", "", mode)["execution"]!["tests"]!));
    }
}
