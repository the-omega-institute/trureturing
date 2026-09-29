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
            var bodyConsumers = file.EndsWith(".cs", StringComparison.Ordinal) ? new[] { RepositoryFileMapProject } : [];
            Assert.Equal(WithRepositoryContract((architecture
                    ? new[] { "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj", RepositoryTopologyProject } : []).Concat(bodyConsumers)),
                Strings(plan["execution"]!["tests"]!));
            Assert.Equal(WithRepositoryContract((architecture
                    ? new[] { "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj", RepositoryTopologyProject }
                    : new[] { "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" }).Concat(bodyConsumers)),
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
    [InlineData("D5/S0/NumberTheory/AdmissionResourceProbe.lean")]
    [InlineData("Meta/Digestion/backfill/admission-resource-probe.json")]
    public void ContentAndMetadataPathsDoNotAcquireUnrelatedEngineeringTests(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan(path, "", mode);
            var readsInstructions = path.StartsWith("D5/", StringComparison.Ordinal);
            var readsDigestion = readsInstructions || path.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal);
            var readsRegistry = readsDigestion || path == "docs/reports/prime-slab-corner-order-0909.json";
            var consumers = OrderedConsumers((readsInstructions ? new[] { InstructionContractProject } : [])
                    .Concat(readsDigestion ? new[] { RepositoryDigestionProject } : [])
                    .Concat(readsRegistry ? new[] { RepositoryFileMapProject } : [])
                    .Concat(path.StartsWith("tools/", StringComparison.Ordinal) || path.EndsWith(".lean", StringComparison.Ordinal) ? new[] { WorktreeContractProject } : [])).ToArray();
            Assert.Equal(consumers, Strings(plan["execution"]!["tests"]!));
            Assert.Equal(consumers.Length == 0 ? "not-required" : "required",
                plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            Assert.DoesNotContain("test-repository-contract", Strings(plan["resources"]!));
        }
    }

    private const string WorktreeContractProject =
        "tools/tests/StrataLint.WorktreeContract.Tests/StrataLint.WorktreeContract.Tests.csproj";

    [Theory]
    [InlineData("push", "A")]
    [InlineData("pr", "A")]
    [InlineData("push", "M")]
    [InlineData("pr", "M")]
    [InlineData("push", "D")]
    [InlineData("pr", "D")]
    [InlineData("push", "R")]
    [InlineData("pr", "R")]
    public void ContentChangesKeepOnlyTheirActualConsumers(string mode, string change)
    {
        foreach (var path in new[] {
            "README.md",
            "docs/develop/theory/WorktreeContractProbe.md",
            "docs/reports/worktree-contract-probe.md",
            "D5/S0/WorktreeContractProbe.lean",
            "Meta/Digestion/backfill/worktree-contract-probe.json",
        })
        {
            var plan = Plan(path, "", mode, change);
            var consumers = path.StartsWith("D5/", StringComparison.Ordinal)
                ? new[] { InstructionContractProject, RepositoryDigestionProject, RepositoryFileMapProject, WorktreeContractProject }
                : path.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal)
                    ? [RepositoryDigestionProject, RepositoryFileMapProject] : [];
            Assert.Equal(WithPathInventory(consumers, change), Strings(plan["execution"]!["tests"]!));
            Assert.DoesNotContain("test-repository-contract", Strings(plan["resources"]!));
            Assert.DoesNotContain("test-cli", Strings(plan["resources"]!));
            var original = Assert.Single(plan["paths"]!.AsArray(), row => row!["path"]!.GetValue<string>() == path);
            Assert.Equal(path.EndsWith(".lean", StringComparison.Ordinal), Strings(original!["require"]!).Contains("test-worktree-contract"));
            if (change == "R")
            {
                var destination = Assert.Single(plan["paths"]!.AsArray(),
                    row => row!["path"]!.GetValue<string>() == "docs/reports/instruction-contract-renamed.md");
                Assert.Equal(new[] { "test-repository-filemap", "test-repository-topology" }, Strings(destination!["require"]!));
            }
        }
    }

    [Theory]
    [InlineData("push", "A")]
    [InlineData("pr", "A")]
    [InlineData("push", "M")]
    [InlineData("pr", "M")]
    [InlineData("push", "D")]
    [InlineData("pr", "D")]
    [InlineData("push", "R")]
    [InlineData("pr", "R")]
    public void WorktreeProgramInputsRetainGuardAcrossEveryChangeKind(string mode, string change)
    {
        foreach (var path in new[] {
            "tools/scripts/agent/openproblem/worktree-guard-probe.py",
            "tools/tests/StrataLint.WorktreeContract.Tests/WorktreeGuardProbe.cs",
            "Blueprint/D5/S0/Carrier/GoldenRatio.scribe.cs",
            "D5/S0/WorktreeContractProbe.lean",
            "Reg/Catalogs/TemplateShadow.lean",
            "Trureturing.lean",
            "docs/reports/worktree-guard-probe.py",
            "docs/reports/worktree-guard-probe.mjs",
            "docs/reports/worktree-guard-probe.c",
            "docs/reports/worktree-guard-probe.cpp",
            "docs/reports/worktree-guard-probe.h",
        })
        {
            var plan = Plan(path, "", mode, change);
            var consumers = new[] { WorktreeContractProject }
                .Concat(path.StartsWith("tools/", StringComparison.Ordinal)
                    ? new[] { "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj" } : [])
                .Concat(path.EndsWith(".cs", StringComparison.Ordinal)
                    ? new[] { RepositoryFileMapProject, RepositoryTopologyProject } : [])
                .Concat(path.StartsWith("D5/", StringComparison.Ordinal)
                    ? new[] { InstructionContractProject, RepositoryDigestionProject, RepositoryFileMapProject } : [])
                .Concat(path.StartsWith("Reg/", StringComparison.Ordinal) || path == "Trureturing.lean"
                    ? new[] { RepositoryFileMapProject } : []);
            Assert.Equal(WithPathInventory(consumers, change), Strings(plan["execution"]!["tests"]!));
            var input = Assert.Single(plan["paths"]!.AsArray(), row => row!["path"]!.GetValue<string>() == path);
            Assert.Contains("test-worktree-contract", Strings(input!["require"]!));
            Assert.Equal(new[] { "test-worktree-contract" }, Strings(input!["path_input_require"]!));
            if (change == "R")
            {
                var destination = Assert.Single(plan["paths"]!.AsArray(),
                    row => row!["path"]!.GetValue<string>() == "docs/reports/instruction-contract-renamed.md");
                Assert.Equal(new[] { "test-repository-filemap", "test-repository-topology" }, Strings(destination!["require"]!));
            }
        }
    }

    private static void AssertNoResourcePlan(System.Text.Json.Nodes.JsonNode plan)
    {
        foreach (var field in new[] { "declared_require", "resources", "selected_stages", "tools", "cache_layers", "materials" })
            Assert.Empty(plan[field]!.AsArray());
        foreach (var field in new[] { "projects", "tests", "checks", "steps", "lean_targets" })
            Assert.Empty(plan["execution"]![field]!.AsArray());
        foreach (var stage in new[] { "build", "engineering", "current" })
            Assert.Equal("not-required", plan["stages"]![stage]!["status"]!.GetValue<string>());
        Assert.Equal(plan["mode"]!.GetValue<string>() == "pr" ? "not-required" : "not-applicable",
            plan["stages"]!["delta"]!["status"]!.GetValue<string>());
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
            Assert.Equal(WithWorktreeContract((architecture ? new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                RepositoryTopologyProject,
            } : []).Concat(file.EndsWith(".cs", StringComparison.Ordinal) ? new[] { RepositoryFileMapProject } : [])),
                Strings(plan["execution"]!["tests"]!));
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
        OrderedConsumers(consumers.Append(WorktreeContractProject));

    private static IEnumerable<string> OrderedConsumers(IEnumerable<string> consumers) =>
        consumers.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal);

    private static IEnumerable<string> WithRepositoryContract(IEnumerable<string> consumers) =>
        WithWorktreeContract(consumers.Append(RepositoryContractProject));
}
