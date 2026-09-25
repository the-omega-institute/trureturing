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
                Projects: new[] { InstructionContractProject, RepositoryDigestionProject, RepositoryFileMapProject, TruthReleaseProject }),
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
            Assert.Equal(WithPathInventory(projects, change), Strings(plan["execution"]!["tests"]!));
            Assert.Equal("required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            var input = Assert.Single(plan["paths"]!.AsArray(), row => row!["path"]!.GetValue<string>() == path);
            Assert.Contains("test-truth-release", Strings(input!["require"]!));
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
            if (change == "R")
            {
                var destination = Assert.Single(plan["paths"]!.AsArray(),
                    row => row!["path"]!.GetValue<string>() == "docs/reports/instruction-contract-renamed.md");
                Assert.Equal(new[] { "test-repository-filemap", "test-repository-topology", "test-worktree-contract" }, Strings(destination!["require"]!));
            }
        }
    }

    [Theory]
    [InlineData("D5/S0/Asymptotics/Bonferroni/TailBounds.lean")]
    [InlineData("D5/S3/Constants/ElementaryExactValues.lean")]
    [InlineData("D5/S3/Midline/GoldenHeatSpectrum.lean")]
    [InlineData("Blueprint/D5/S3/Midline/GoldenHeatSpectrum.md")]
    [InlineData("Blueprint/D5/S3/Midline/GoldenHeatSpectrum.scribe.cs")]
    public void UnrelatedContentSelectsOnlyItsActualConsumers(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan(path, "", mode);
            var consumers = path.EndsWith(".lean", StringComparison.Ordinal)
                ? new[] { InstructionContractProject, RepositoryDigestionProject, RepositoryFileMapProject }
                : path.EndsWith(".scribe.cs", StringComparison.Ordinal)
                    ? new[] { RepositoryContractProject, RepositoryFileMapProject, RepositoryTopologyProject }
                    : [];
            Assert.Equal(WithWorktreeContract(consumers), Strings(plan["execution"]!["tests"]!));
            Assert.DoesNotContain("test-cover-batch", Strings(plan["resources"]!));
            Assert.DoesNotContain("test-truth-release", Strings(plan["resources"]!));
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
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
