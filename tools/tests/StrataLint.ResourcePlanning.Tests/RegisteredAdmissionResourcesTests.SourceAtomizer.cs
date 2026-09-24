using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string SourceAtomizerProject =
        "tools/tests/StrataLint.SourceAtomizer.Tests/StrataLint.SourceAtomizer.Tests.csproj";

    [Theory]
    [InlineData("TheoryAtomizerTests.cs")]
    [InlineData("AssemblyInfo.cs")]
    [InlineData("Usings.cs")]
    [InlineData("StrataLint.SourceAtomizer.Tests.csproj")]
    public void SourceAtomizerSourcesSelectTheirCompleteProject(string file)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                RepositoryTopologyProject,
                SourceAtomizerProject,
            }.Concat(file.EndsWith(".cs", StringComparison.Ordinal)
                ? new[] { "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj" } : [])), Strings(Plan($"tools/tests/StrataLint.SourceAtomizer.Tests/{file}", "", mode)["execution"]!["tests"]!));
    }

    [Fact]
    public void SourceAtomizerLockSelectsItsCompleteProject()
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(new[] { SourceAtomizerProject }),
                Strings(Plan("tools/tests/StrataLint.SourceAtomizer.Tests/packages.lock.json", "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/TestSupport/StrataLint.DigestionTestSupport/TheoryAtomizerAssertions.cs", "StrataLint.ArchitectureTests,StrataLint.CoverBatch.Tests,StrataLint.Digestion.Tests,StrataLint.RepositoryTopology.Tests,StrataLint.SourceAtomizer.Tests,StrataLint.Tests,StrataLint.TruthRelease.Tests")]
    [InlineData("tools/TestSupport/StrataLint.CliTestSupport/FakeScribeEmissionVerifier.cs", "StrataLint.ArchitectureTests,StrataLint.CliIntegration.Tests,StrataLint.CoverBatch.Tests,StrataLint.RepositoryTopology.Tests,StrataLint.SourceAtomizer.Tests,StrataLint.Tests,StrataLint.TruthRelease.Tests")]
    public void SourceAtomizerSharedHelpersSelectAllRegisteredConsumers(string path, string consumers)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithWorktreeContract(consumers.Split(',').Append("StrataLint.RepositoryFileMap.Tests").Select(name => $"tools/tests/{name}/{name}.csproj")),
                Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Fact]
    public void AtomizerConfigurationRetainsEngineeringAndExplicitConsumers()
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(new[] { "delta", "engineering", "filemap", "test-cover-batch", "test-digestion", "test-rules", "test-source-atomizer", "test-truth-release", "test-worktree-contract" },
                Strings(Plan("Meta/Digestion/atomizers.toml", "", mode)["declared_require"]!));
    }

    [Theory]
    [InlineData("push", "M")]
    [InlineData("pr", "M")]
    [InlineData("push", "D")]
    [InlineData("pr", "D")]
    [InlineData("push", "R")]
    [InlineData("pr", "R")]
    public void SourceAtomizerRuntimeChangesSelectItsCompleteProject(string mode, string change)
    {
        foreach (var path in new[]
        {
            "docs/develop/theory/INTERFACE_PAPER.md",
            "docs/develop/theory/INTERFACE_PHILOSOPHY.md",
            "docs/develop/theory/PERIODIC_TREE_registry.jsonl",
            "Meta/Digestion/backfill/periodic-tree-registry/source.toml",
            "Meta/Digestion/backfill/periodic-tree-registry/residual-open/ecd939e3d6a40f5626c00cc22c4584169e449dcd8e76d971c7f9ade9b1d4f901.yaml",
            "Meta/Digestion/atoms/sha256/ecd939e3d6a40f5626c00cc22c4584169e449dcd8e76d971c7f9ade9b1d4f901",
        })
        {
            var plan = Plan(path, "", mode, change);
            var readsBackfill = path.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal);
            Assert.Equal(WithWorktreeContract(new[] { SourceAtomizerProject }.Concat(readsBackfill ? new[] { RepositoryDigestionProject } : [])), Strings(plan["execution"]!["tests"]!));
            Assert.Equal((readsBackfill ? new[] { "test-repository-digestion", "test-source-atomizer", "test-worktree-contract" } : new[] { "test-source-atomizer", "test-worktree-contract" }),
                Strings(plan["stages"]!["engineering"]!["resources"]!));
            Assert.Equal("required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            var input = Assert.Single(plan["paths"]!.AsArray(), row => row!["path"]!.GetValue<string>() == path);
            Assert.Contains("test-source-atomizer", Strings(input!["require"]!));
            if (change == "R")
            {
                var destination = Assert.Single(plan["paths"]!.AsArray(),
                    row => row!["path"]!.GetValue<string>() == "docs/reports/instruction-contract-renamed.md");
                Assert.Equal(new[] { "test-worktree-contract" }, Strings(destination!["require"]!));
            }
        }
    }
}
