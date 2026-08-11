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
    private const string C0CertificatePath =
        "Meta/StrataLint/Golden/c0-inaugural-conservative-certificate.json";

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
        FrozenLedgerChangeClassifier.AcceptedRoot,
        C0CertificatePath,
        SolutionPath,
        EngineProjectPath,
        "global.json",
        "Directory.Build.props",
        "Directory.Packages.props",
        EngineLockPath,
        RawDefinitionSourcePath,
        "lean-toolchain",
        ".github/CODEOWNERS",
        RuleFixture.WorkflowPath,
        RuleFixture.HarnessGatePath,
    };

    public static TheoryData<string> DataPaths => new()
    {
        "Meta/BACKFILL.yaml",
        "Meta/FILEMAP.toml",
        RuleFixture.GoldenDataSourcePath,
        C0CeremonyProjection.ValuesKernelDataPath,
        GoldenFixtureRegistryLoader.RelativePath,
        "Library/queries.yaml",
    };

    [Theory]
    [MemberData(nameof(ProtectedPaths))]
    public void Sl022RequiresBaseOwnedVerificationForEveryProtectedSurface(string path)
    {
        var changes = RawChangeSet.Create(new[] { path });

        var outcome = BootstrapGate.Evaluate(changes);

        var verification = Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(outcome);
        Assert.Contains(verification.ChangeSet.Paths, item => item.Value == path);
        var profile = MetaEvaluationProfile.ForProtectedSurface(verification.ChangeSet);
        Assert.Null(profile.ClearCapability);
        Assert.Same(verification.ChangeSet, profile.ProtectedChangeSet);
    }

    [Fact]
    public void Sl022StillClassifiesEngineSourceAsMetaProgram()
    {
        var changes = RawChangeSet.Create(new[] { EngineGidSourcePath });

        var outcome = BootstrapGate.Evaluate(changes);

        Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(outcome);
    }

    [Theory]
    [InlineData(RuleFixture.DefinitionsProjectPath)]
    [InlineData(RuleFixture.DefinitionsLockPath)]
    public void Sl022KeepsRetiredDefinitionsPrefixOnTheBaseCompatibleContentPath(string path)
    {
        var changes = RawChangeSet.Create(new[] { path });

        var outcome = BootstrapGate.Evaluate(changes);

        Assert.IsType<BootstrapOutcome.Clear>(outcome);
    }

    [Theory]
    [InlineData(RuleFixture.BlueprintPath)]
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

        Assert.Equal(25, descriptors.Length);
        Assert.Equal(25, descriptors.Select(item => item.Id).Distinct().Count());
        Assert.Equal(
            Enumerable.Range(1, 23).Select(RuleId.CreateKnown).Append(RuleId.CreateKnown(25)).Append(RuleId.CreateKnown(26)),
            descriptors.Select(item => item.Id));
        Assert.Equal(AdmissionEffect.HumanGate, descriptors[21].AdmissionEffect);
        Assert.All(
            descriptors.Where(item => item.Id.Value is not ("SL-007" or "SL-009" or "SL-014" or "SL-022" or "SL-023")),
            item => Assert.Equal(AdmissionEffect.Block, item.AdmissionEffect));
        Assert.Equal(AdmissionEffect.Observe, descriptors[22].AdmissionEffect);
        Assert.All(
            descriptors.Where(item => item.Id.Value is "SL-007" or "SL-009" or "SL-014"),
            item => Assert.Equal(RuleLifecycle.Deferred, item.Lifecycle));
    }
}
