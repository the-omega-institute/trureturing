using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TrustTopologyTests
{
    private const string EngineGidSourcePath =
        "Meta/StrataLint/StrataLint.Engine/Coordinates/Gid.cs";
    private const string CliProgramSourcePath = "Meta/StrataLint/StrataLint.Cli/Program.cs";
    private const string ThisTestSourcePath =
        "Meta/StrataLint/StrataLint.Tests/Admission/TrustTopologyTests.cs";
    private const string SolutionPath = WorktreeCommand.SolutionPath;
    private const string EngineProjectPath =
        "Meta/StrataLint/StrataLint.Engine/StrataLint.Engine.csproj";
    private const string EngineLockPath =
        "Meta/StrataLint/StrataLint.Engine/packages.lock.json";
    private const string RawDefinitionSourcePath = "Blueprint/D5/S1/Digit/Raw.scribe.cs";

    public static TheoryData<string> ProtectedPaths => new()
    {
        EngineGidSourcePath,
        CliProgramSourcePath,
        ThisTestSourcePath,
        RuleFixture.SpecificationPath,
        "Meta/registry.yaml",
        "Meta/domains.yaml",
        RuleFixture.HeartsPath,
        RepositoryPathPolicy.AssumptionRegistryPath,
        "Meta/StrataLint/Golden/rules.json",
        SolutionPath,
        EngineProjectPath,
        "global.json",
        "Directory.Build.props",
        "Directory.Packages.props",
        EngineLockPath,
        "lean-toolchain",
        ".github/CODEOWNERS",
        RuleFixture.WorkflowPath,
        RuleFixture.HarnessGatePath,
    };

    [Theory]
    [MemberData(nameof(ProtectedPaths))]
    public void Sl022RequiresExternalHumanReviewForEveryProtectedSurface(string path)
    {
        var changes = RawChangeSet.Create(new[] { path });

        var outcome = BootstrapGate.Evaluate(changes);

        var required = Assert.IsType<BootstrapOutcome.HumanReviewRequired>(outcome);
        Assert.Contains(required.ChangeSet.Paths, item => item.Value == path);
        var profile = MetaEvaluationProfile.ForProtectedSurface(required.ChangeSet);
        Assert.Null(profile.ClearCapability);
        Assert.Same(required.ChangeSet, profile.ProtectedChangeSet);
    }

    [Theory]
    [InlineData(RuleFixture.BlueprintPath)]
    [InlineData(RawDefinitionSourcePath)]
    public void ContentContributionProducesAnUnforgeableMetaClearCapability(string path)
    {
        var changes = RawChangeSet.Create(new[] { path });

        var outcome = BootstrapGate.Evaluate(changes);

        var clear = Assert.IsType<BootstrapOutcome.Clear>(outcome);
        Assert.NotNull(clear.Capability);
        Assert.Empty(typeof(MetaClear).GetConstructors());
    }

    [Fact]
    public void RuleCatalogIsExplicitCompleteAndCannotDowngradeEffectsFromConfiguration()
    {
        var descriptors = RuleCatalog.Default.Descriptors;

        Assert.Equal(22, descriptors.Length);
        Assert.Equal(22, descriptors.Select(item => item.Id).Distinct().Count());
        Assert.Equal(
            Enumerable.Range(1, 22).Select(RuleId.CreateKnown),
            descriptors.Select(item => item.Id));
        Assert.Equal(AdmissionEffect.HumanGate, descriptors[21].AdmissionEffect);
        Assert.All(
            descriptors.Where(item => item.Id.Value is not ("SL-007" or "SL-009" or "SL-014" or "SL-022")),
            item => Assert.Equal(AdmissionEffect.Block, item.AdmissionEffect));
        Assert.All(
            descriptors.Where(item => item.Id.Value is "SL-007" or "SL-009" or "SL-014"),
            item => Assert.Equal(RuleLifecycle.Deferred, item.Lifecycle));
    }
}
