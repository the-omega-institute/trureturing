using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
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
            "CLAUDE.md" => ["StrataLint.PrScript.Tests"],
            "tools/scripts/agent/batch_pr.sh" => ["StrataLint.Tests"],
            _ => Array.Empty<string>(),
        });
        Assert.Equal(WithRepositoryContract(consumers.Select(name => $"tools/tests/{name}/{name}.csproj")),
            Strings(plan["execution"]!["tests"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
    }
}
