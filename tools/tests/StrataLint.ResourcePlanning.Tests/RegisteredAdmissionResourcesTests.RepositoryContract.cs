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
                    ? new[] { "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj", "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj", RepositoryTopologyProject } : []),
                Strings(plan["execution"]!["tests"]!));
            Assert.Equal(WithRepositoryContract(architecture
                    ? new[] { "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj", "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj", RepositoryTopologyProject }
                    : new[] { "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" }),
                Strings(plan["execution"]!["projects"]!));
            Assert.DoesNotContain("test-cli", Strings(plan["resources"]!));
        }
    }

    [Theory]
    [InlineData("tools/scripts/agent/merge-gate.sh", "StrataLint.ArchitectureTests", null)]
    [InlineData("tools/tests/StrataLint.Configuration.Tests/RegistryTests.cs", "StrataLint.ArchitectureTests", "StrataLint.Configuration.Tests")]
    [InlineData("tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py", "StrataLint.Cache.Release.Tests", null)]
    public void EngineeringPathsSelectOnlyTheirActualContractConsumers(string path, string first, string? second)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var consumers = new[] { first }.Concat(second is null ? [] : new[] { second })
                .Concat(path == "tools/scripts/agent/merge-gate.sh" ? new[] { "StrataLint.RepositoryContract.Tests" } : [])
                .Concat(path.EndsWith(".cs", StringComparison.Ordinal) ? new[] { "StrataLint.RepositoryFileMap.Tests", "StrataLint.RepositoryTopology.Tests" } : []);
            Assert.Equal(WithWorktreeContract(consumers.Select(name => $"tools/tests/{name}/{name}.csproj")),
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
    public void ContentAndMetadataPathsDoNotAcquireUnrelatedEngineeringTests(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan(path, "", mode);
            var readsInstructions = path.StartsWith("D5/", StringComparison.Ordinal);
            var readsDigestion = readsInstructions || path.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal);
            Assert.Equal(WithWorktreeContract((readsInstructions ? new[] { InstructionContractProject } : [])
                    .Concat(readsDigestion ? new[] { RepositoryDigestionProject } : [])),
                Strings(plan["execution"]!["tests"]!));
            Assert.Equal("required",
                plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            Assert.DoesNotContain("test-repository-contract", Strings(plan["resources"]!));
        }
    }

    private const string WorktreeContractProject =
        "tools/tests/StrataLint.WorktreeContract.Tests/StrataLint.WorktreeContract.Tests.csproj";

    [Theory]
    [InlineData("push", "M")]
    [InlineData("pr", "M")]
    [InlineData("push", "D")]
    [InlineData("pr", "D")]
    [InlineData("push", "R")]
    [InlineData("pr", "R")]
    public void WholeRepositoryTextChangesKeepTheirCompleteConsumer(string mode, string change)
    {
        foreach (var path in new[] {
            "README.md",
            "docs/develop/theory/WorktreeContractProbe.md",
            "docs/reports/worktree-contract-probe.md",
            "D5/WorktreeContractProbe.lean",
            "Meta/Digestion/backfill/worktree-contract-probe.json",
        })
        {
            var plan = Plan(path, "", mode, change);
            Assert.Equal(WithWorktreeContract(path.StartsWith("D5/", StringComparison.Ordinal)
                ? new[] { InstructionContractProject } : []), Strings(plan["execution"]!["tests"]!));
            Assert.DoesNotContain("test-repository-contract", Strings(plan["resources"]!));
            Assert.DoesNotContain("test-cli", Strings(plan["resources"]!));
            var original = Assert.Single(plan["paths"]!.AsArray(), row => row!["path"]!.GetValue<string>() == path);
            Assert.Contains("test-worktree-contract", Strings(original!["require"]!));
            if (change == "R")
            {
                var destination = Assert.Single(plan["paths"]!.AsArray(),
                    row => row!["path"]!.GetValue<string>() == "docs/reports/instruction-contract-renamed.md");
                Assert.Equal(new[] { "test-worktree-contract" }, Strings(destination!["require"]!));
            }
        }
    }

    [Theory]
    [InlineData("WorktreeCacheStrategyTests.cs", true)]
    [InlineData("StrataLint.WorktreeContract.Tests.csproj", true)]
    [InlineData("packages.lock.json", false)]
    public void WorktreeContractChangesKeepItsCompleteProjectWithoutCliLinkage(string file, bool architecture)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan("tools/tests/StrataLint.WorktreeContract.Tests/" + file, "", mode);
            Assert.Equal(WithWorktreeContract(architecture ? new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                "tools/tests/StrataLint.RepositoryFileMap.Tests/StrataLint.RepositoryFileMap.Tests.csproj",
                RepositoryTopologyProject,
            } : []), Strings(plan["execution"]!["tests"]!));
            Assert.DoesNotContain("test-repository-contract", Strings(plan["resources"]!));
        }
    }

    private static void AssertWorktreeOnlyPlan(System.Text.Json.Nodes.JsonNode plan)
    {
        Assert.Equal(new[] { "build", "test-worktree-contract" }, Strings(plan["resources"]!));
        Assert.Equal(new[] { "build", "engineering" }, Strings(plan["selected_stages"]!));
        Assert.Equal(new[] { "bash", "dotnet", "git", "python3" }, Strings(plan["tools"]!));
        Assert.Equal(new[] { "engineering", "judge" }, Strings(plan["cache_layers"]!));
        Assert.Equal(new[] { WorktreeContractProject }, Strings(plan["execution"]!["tests"]!));
        Assert.Equal(new[] {
            "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
            WorktreeContractProject,
        }, Strings(plan["execution"]!["projects"]!));
        foreach (var stage in new[] { "build", "engineering" })
            Assert.Equal("required", plan["stages"]![stage]!["status"]!.GetValue<string>());
        Assert.Equal("not-required", plan["stages"]!["current"]!["status"]!.GetValue<string>());
        Assert.Equal(plan["mode"]!.GetValue<string>() == "pr" ? "not-required" : "not-applicable",
            plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        foreach (var field in new[] { "checks", "steps", "lean_targets" })
            Assert.Empty(plan["execution"]![field]!.AsArray());
    }

    private static IEnumerable<string> WithWorktreeContract(IEnumerable<string> consumers) =>
        consumers.Append(WorktreeContractProject).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal);

    private static IEnumerable<string> WithRepositoryContract(IEnumerable<string> consumers) =>
        WithWorktreeContract(consumers.Append(RepositoryContractProject));
}
