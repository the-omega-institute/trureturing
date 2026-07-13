using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TypeModelTests
{
    private const string RawDefinitionSourcePath = "Blueprint/D5/S1/Digit/Raw.scribe.cs";
    private const string FkstMonitorSkillPath = ".claude/skills/fkst-monitor/SKILL.md";

    [Fact]
    public void GidRejectsUnsafeMachineCharacters()
    {
        Assert.False(Gid.TryParse("D5/S0/Carrier/Ring@bad", out _));
    }

    [Fact]
    public void RepoPathRejectsTraversalAndBackslashes()
    {
        Assert.False(RepoPath.TryCreate("../D5/S0/Carrier/Ring.lean", out _));
        Assert.False(RepoPath.TryCreate("D5\\S0\\Carrier\\Ring.lean", out _));
    }

    [Fact]
    public void RuleAndCaseIdsAreClosedByGrammar()
    {
        Assert.True(RuleId.TryCreate("SL-022", out _));
        Assert.False(RuleId.TryCreate("SL-023", out _));
        Assert.True(CaseId.TryCreate("D5-T0016", out _));
    }

    [Fact]
    public void ValidationProfilesAreAClosedUnion()
    {
        ValidationProfile profile = new ValidationProfile.StructuredJson();
        Assert.Equal("structured-json", profile.Match(
            structuredJson: static _ => "structured-json",
            structuredYaml: static _ => "structured-yaml",
            leanModule: static _ => "lean-module",
            opaqueText: static _ => "opaque-text"));
    }

    [Theory]
    [InlineData("D5/S0/Carrier/Ring", RuleFixture.RingPath)]
    [InlineData("D5/S0/Carrier/Ring.norm_mul", RuleFixture.RingPath)]
    [InlineData("D5/B/S0/Carrier/Ring", RuleFixture.BlueprintPath)]
    [InlineData("D5/E/S0/Carrier/Ring.result--json", "Evidence/D5/S0/Carrier/Ring.result.json")]
    [InlineData("D5/E/values--json", "Evidence/D5/values.json")]
    [InlineData("D5/E/values.result--json", "Evidence/D5/values.result.json")]
    [InlineData("D5/E/experiments/D5-X0001.spec--yaml", "Evidence/D5/experiments/D5-X0001.spec.yaml")]
    [InlineData("D5/C/2026-07-11/r168", "Chronicle/2026/07/11-r168.md")]
    [InlineData("D5/L/bellissard1992gap", "Library/notes/bellissard1992gap.md")]
    [InlineData("D5/P/D5-P001", "Papers/recipes/D5-P001.yaml")]
    [InlineData("D5/P/D5-P001--frozen", "Papers/frozen/D5-P001/manifest.sha256")]
    public void GidAndTargetAreCanonicalTwoWayMappings(string text, string path)
    {
        Assert.True(Gid.TryParse(text, out var gid));
        Assert.Equal(path, gid.Path.Value);

        var target = gid.ToTarget();
        var printed = Gid.FromTarget(target);

        Assert.Equal(gid, printed);
        Assert.Equal(target, printed.ToTarget());
        Assert.Equal(text, printed.Value);
    }

    [Theory]
    [InlineData("D5/E/../Ring.result--json")]
    [InlineData("D5/E/./Ring.result--json")]
    [InlineData("D5/E/foo//Ring.result--json")]
    [InlineData("D5/E/S0/Carrier/Ring--json")]
    [InlineData("D5/B/S0/Carrier/Ring.declaration")]
    [InlineData("D8/S0/Carrier/Ring")]
    public void GidRejectsUnsafeOrNoncanonicalNeighbors(string text)
    {
        Assert.False(Gid.TryParse(text, out _));
    }

    [Fact]
    public void BlueprintDefinitionSourceIsContentButNotASecondSemanticTarget()
    {
        var path = RepoPath.CreateKnown(RawDefinitionSourcePath);

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    [Fact]
    public void BlueprintDefinitionSourceStillObeysCanonicalAddressGrammar()
    {
        var path = RepoPath.CreateKnown("Blueprint/D5/S1/Digit/raw.scribe.cs");

        Assert.NotNull(RepositoryPathPolicy.Validate(path, Policy()));
    }

    [Fact]
    public void HarnessGateScriptIsClosedWorldRegisteredAndBootstrapProtected()
    {
        const string value = RuleFixture.HarnessGatePath;
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        var outcome = BootstrapGate.Evaluate(RawChangeSet.Create(new[] { value }));
        var required = Assert.IsType<BootstrapOutcome.HumanReviewRequired>(outcome);
        Assert.Contains(required.ChangeSet.Paths, item => item == path);
    }

    [Fact]
    public void MakefileIsClosedWorldRegisteredAndBootstrapProtected()
    {
        const string value = "Makefile";
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        var outcome = BootstrapGate.Evaluate(RawChangeSet.Create([value]));
        var required = Assert.IsType<BootstrapOutcome.HumanReviewRequired>(outcome);
        Assert.Contains(required.ChangeSet.Paths, item => item == path);
    }

    [Fact]
    public void FkstIntegrationLayerIsClosedWorldRegistered()
    {
        var path = RepoPath.CreateKnown(".fkst/fkst.workspace.toml");

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    [Fact]
    public void ClaudeSkillsLayerIsClosedWorldRegistered()
    {
        var path = RepoPath.CreateKnown(FkstMonitorSkillPath);

        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    private static ValidatedPolicy Policy() =>
        Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
}
