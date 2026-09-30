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
    public void EngineeringPathsSelectOnlyTheirActualContractConsumers(string path, string first, string? second)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var consumers = new[] { first }.Concat(second is null ? [] : new[] { second })
                .Concat(path == "tools/scripts/agent/merge-gate.sh" ? new[] { "StrataLint.RepositoryContract.Tests" } : [])
                .Concat(path.EndsWith(".cs", StringComparison.Ordinal) ? new[] { "StrataLint.RepositoryFileMap.Tests", "StrataLint.RepositoryTopology.Tests" } : []);
            Assert.Equal(OrderedConsumers(consumers.Select(name => $"tools/tests/{name}/{name}.csproj")),
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
                    .Concat(readsRegistry ? new[] { RepositoryFileMapProject } : [])).ToArray();
            Assert.Equal(consumers, Strings(plan["execution"]!["tests"]!));
            Assert.Equal(consumers.Length == 0 ? "not-required" : "required",
                plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            Assert.DoesNotContain("test-repository-contract", Strings(plan["resources"]!));
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
                ? new[] { InstructionContractProject, RepositoryDigestionProject, RepositoryFileMapProject }
                : path.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal)
                    ? [RepositoryDigestionProject, RepositoryFileMapProject] : [];
            Assert.Equal(WithPathInventory(consumers, change), Strings(plan["execution"]!["tests"]!));
            Assert.DoesNotContain("test-repository-contract", Strings(plan["resources"]!));
            Assert.DoesNotContain("test-cli", Strings(plan["resources"]!));
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

    private static IEnumerable<string> OrderedConsumers(IEnumerable<string> consumers) =>
        consumers.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal);

    private static IEnumerable<string> WithRepositoryContract(IEnumerable<string> consumers) =>
        OrderedConsumers(consumers.Append(RepositoryContractProject));
}
