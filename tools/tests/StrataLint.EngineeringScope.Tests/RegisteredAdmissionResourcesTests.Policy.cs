using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("tools/scripts/agent/merge-gate.sh", "push")]
    [InlineData("tools/scripts/agent/merge-gate.sh", "pr")]
    [InlineData("tools/scripts/agent/openproblem/erdos617.py", "push")]
    [InlineData("tools/scripts/agent/openproblem/erdos617.py", "pr")]
    [InlineData("tools/scripts/agent/openproblem/standing-check.py", "pr")]
    [InlineData("tools/scripts/agent/openproblem/TARGET-GATES.md", "pr")]
    public void RegisteredAgentToolsKeepDataChecksWithoutUnrelatedTestPrograms(string path, string mode)
    {
        var plan = Plan(path, "", mode);
        Assert.Equal(mode == "pr" ? new[] { "build", "current-data", "delta-data", "filemap" }
            : new[] { "build", "current-data", "filemap" }, Strings(plan["resources"]!));
        Assert.Equal(new[] { "SL-003", "filemap" }, Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
        Assert.Equal("not-required", plan["stages"]!["engineering"]!["status"]!.GetValue<string>());
        Assert.DoesNotContain("lake", Strings(plan["tools"]!));
    }

    [Theory]
    [InlineData("CLAUDE.md", "push")]
    [InlineData("CLAUDE.md", "pr")]
    [InlineData("skills/codex-formal-answer/SKILL.md", "pr")]
    [InlineData("skills/codex-theory-ingest/SKILL.md", "pr")]
    public void PolicyTextRunsItsRepositoryContractsWithoutFixtureSuites(string path, string mode)
    {
        var plan = Plan(path, "", mode);
        Assert.Contains("repository", Strings(plan["resources"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        Assert.Equal(new[] { "SL-003", "SL-015", "SL-019", "filemap" }, Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
        Assert.Equal(new[] { "tools/tests/StrataLint.Repository.Tests/StrataLint.Repository.Tests.csproj" },
            Strings(plan["execution"]!["projects"]!).Where(path => path.StartsWith("tools/tests/", StringComparison.Ordinal)));
        Assert.DoesNotContain("lake", Strings(plan["tools"]!));
    }

    [Theory]
    [InlineData("Meta/domains.yaml", "push")]
    [InlineData("Meta/domains.yaml", "pr")]
    [InlineData("Meta/registry.yaml", "pr")]
    public void RegistryDataRetainsSemanticConsumersWithoutEngineeringFixtures(string path, string mode)
    {
        var plan = Plan(path, "", mode);
        Assert.Contains("current", Strings(plan["resources"]!));
        Assert.Contains("repository", Strings(plan["resources"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
        Assert.DoesNotContain("selftest-pair", Strings(plan["execution"]!["checks"]!));
        Assert.DoesNotContain("capability-proof", Strings(plan["execution"]!["checks"]!));
        Assert.DoesNotContain("banned-api-proof", Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "tools/tests/StrataLint.Repository.Tests/StrataLint.Repository.Tests.csproj" },
            Strings(plan["execution"]!["projects"]!).Where(path => path.StartsWith("tools/tests/", StringComparison.Ordinal)));
        if (mode == "pr") Assert.Contains("delta-registry", Strings(plan["resources"]!));
    }
}
