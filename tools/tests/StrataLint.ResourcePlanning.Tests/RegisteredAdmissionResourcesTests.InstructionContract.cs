using System.Text.Json.Nodes;
using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string InstructionContractProject =
        "tools/tests/StrataLint.InstructionContract.Tests/StrataLint.InstructionContract.Tests.csproj";

    [Theory]
    [InlineData("skills/codex-formal-answer/SKILL.md", "push")]
    [InlineData("skills/codex-formal-answer/SKILL.md", "pr")]
    [InlineData("skills/codex-theory-ingest/SKILL.md", "push")]
    [InlineData("skills/codex-theory-ingest/SKILL.md", "pr")]
    [InlineData("CLAUDE.md", "push")]
    [InlineData("CLAUDE.md", "pr")]
    [InlineData("tools/scripts/agent/batch_pr.sh", "push")]
    [InlineData("tools/scripts/agent/batch_pr.sh", "pr")]
    public void InstructionInputsSelectTheirCompleteContractConsumers(string path, string mode)
    {
        var plan = Plan(path, "", mode);
        var consumers = new[] { "StrataLint.InstructionContract.Tests" }.Concat(path switch
        {
            "CLAUDE.md" => ["StrataLint.PrScript.Tests", "StrataLint.Tests"],
            _ => Array.Empty<string>(),
        });
        Assert.Equal(WithWorktreeContract(consumers.Concat(path == "tools/scripts/agent/batch_pr.sh" ? new[] { "StrataLint.RepositoryContract.Tests" } : []).Select(name => $"tools/tests/{name}/{name}.csproj")),
            Strings(plan["execution"]!["tests"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
    }

    [Theory]
    [InlineData("push", "M")]
    [InlineData("pr", "M")]
    [InlineData("push", "D")]
    [InlineData("pr", "D")]
    [InlineData("push", "R")]
    [InlineData("pr", "R")]
    public void TrackedD5InputsSelectTheirCompleteInstructionAndRuntimeConsumers(string mode, string change)
    {
        foreach (var path in new[]
        {
            "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure.lean",
            "D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling.lean",
            "D5/S0/NumberTheory/AdmissionResourceProbe.lean",
            "D5/InstructionContractProbe.md",
        })
        {
            var plan = Plan(path, "", mode, change);
            Assert.Equal(WithPathInventory(path.EndsWith(".lean", StringComparison.Ordinal)
                    ? new[] { InstructionContractProject, RepositoryDigestionProject, RepositoryFileMapProject }
                    : new[] { InstructionContractProject }, change), Strings(plan["execution"]!["tests"]!));
            Assert.Equal((path.EndsWith(".lean", StringComparison.Ordinal)
                    ? new[] { "test-instruction-contract", "test-repository-digestion", "test-repository-filemap", "test-worktree-contract" }
                    : new[] { "test-instruction-contract", "test-worktree-contract" })
                    .Concat(change is "D" or "R" ? new[] { "test-repository-filemap", "test-repository-topology" } : [])
                    .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal),
                Strings(plan["stages"]!["engineering"]!["resources"]!));
            Assert.Equal("required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
            var input = Assert.Single(plan["paths"]!.AsArray(), row => row!["path"]!.GetValue<string>() == path);
            Assert.Contains("test-instruction-contract", Strings(input!["require"]!));
            if (change == "R")
            {
                var destination = Assert.Single(plan["paths"]!.AsArray(),
                    row => row!["path"]!.GetValue<string>() == "docs/reports/instruction-contract-renamed.md");
                Assert.Equal(new[] { "test-repository-filemap", "test-repository-topology", "test-worktree-contract" }, Strings(destination!["require"]!));
            }
        }
    }

    [Fact]
    public void InstructionStageProvisionsGitForItsTrackedInputReader()
    {
        var result = Python(basis.Path, """
            import json, pathlib, sys
            source, root = map(pathlib.Path, sys.argv[1:3])
            sys.path.insert(0, str(source / 'tools/scripts/workflow'))
            import ci_plan
            plan = {'stages': {'engineering': {
                'status': 'required', 'resources': ['test-instruction-contract']}}}
            print(json.dumps(ci_plan.stage_requirements(root, plan, 'engineering')))
            """);
        Assert.True(result.Exit == 0, result.Text);
        var requirements = JsonNode.Parse(result.Text)!;
        Assert.True(requirements["required"]!.GetValue<bool>());
        Assert.Contains("git", Strings(requirements["tools"]!));
    }
}
