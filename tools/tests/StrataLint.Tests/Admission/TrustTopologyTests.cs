using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TrustTopologyTests
{
    private const string EngineGidSourcePath =
        "tools/StrataLint.Engine/Coordinates/Gid.cs";
    private const string CliProgramSourcePath = "tools/StrataLint.Cli/Program.cs";
    private const string ThisTestSourcePath =
        "tools/tests/StrataLint.Tests/Admission/TrustTopologyTests.cs";
    private const string SolutionPath = WorktreeCommand.SolutionPath;
    private const string EngineProjectPath =
        "tools/StrataLint.Engine/StrataLint.Engine.csproj";
    private const string EngineLockPath =
        "tools/StrataLint.Engine/packages.lock.json";
    private const string RawDefinitionSourcePath = "Blueprint/D5/S1/Digit/Raw.scribe.cs";
    private const string BootstrapGatePath =
        "tools/StrataLint.Engine/Admission/BootstrapGate.cs";
    private const string BlueprintSourcePath = "Blueprint/D5/S0/Carrier/Ring.scribe.cs";
    private const string BlueprintProjectionPath = "Blueprint/D5/S0/Carrier/Ring.md";
    private const string UnprotectedTruthGraphPath = "Generated/truth-graph.v1.json";
    private const string ProtectedScribeEmissionsPath =
        "tools/Generated/scribe-emissions.v1.json";
    private const string ProtectedAnchorCatalogPath =
        "tools/Generated/anchor-catalog.v1.json";

    public static TheoryData<string> ProtectedPaths => new()
    {
        EngineGidSourcePath,
        CliProgramSourcePath,
        ThisTestSourcePath,
        "Meta/registry.yaml",
        "Meta/domains.yaml",
        RuleFixture.HeartsPath,
        RepositoryPathPolicy.AssumptionRegistryPath,
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
        "Golden/values-kernels.toml",
        TestRegistry.RelativePath,
        "Library/queries.yaml",
    };

    [Theory]
    [InlineData(BootstrapGatePath, true)]
    [InlineData(BlueprintSourcePath, true)]
    [InlineData(BlueprintProjectionPath, false)]
    public void DeclarativeProtectionPolicyPreservesTheExistingPredicate(
        string rawPath,
        bool expected)
    {
        var path = Assert.IsType<RepoPath>(RepoPath.TryCreate(rawPath, out var parsed) ? parsed : null);

        Assert.Equal(expected, BootstrapProtectionPolicy.IsProtected(path));
        Assert.Equal(expected, BootstrapGate.IsProtected(path));
    }

    [Fact]
    public void TopLevelTruthGraphChangeDoesNotProduceSl022Diagnostics()
    {
        var clear = Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(RawChangeSet.Create([UnprotectedTruthGraphPath])));

        Assert.NotNull(clear.Capability);
    }

    [Fact]
    public void AddedAcceptedFragmentDoesNotProduceSl022Diagnostics()
    {
        var path = FrozenLedgerChangeClassifier.AcceptedPath(
            "sha256:" + new string('a', 64));

        var clear = Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(RawChangeSet.Create([path])));

        Assert.NotNull(clear.Capability);
    }

    [Fact]
    public void BaseJudgeScribeEmissionsInputProducesExactSl022Diagnostic()
    {
        AssertExactSl022Diagnostic(ProtectedScribeEmissionsPath);
    }

    [Fact]
    public void BaseJudgeAnchorCatalogInputProducesExactSl022Diagnostic()
    {
        AssertExactSl022Diagnostic(ProtectedAnchorCatalogPath);
    }

    [Theory]
    [MemberData(nameof(ProtectedPaths))]
    [BaseFactScopeProbe(22)]
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

        Assert.Equal(28, descriptors.Length);
        Assert.Equal(28, descriptors.Select(item => item.Id).Distinct().Count());
        Assert.Equal(
            Enumerable.Range(1, 23).Select(RuleId.CreateKnown)
                .Append(RuleId.CreateKnown(25))
                .Append(RuleId.CreateKnown(26))
                .Append(RuleId.CreateKnown(28))
                .Append(RuleId.CreateKnown(29))
                .Append(RuleId.CreateKnown(30)),
            descriptors.Select(item => item.Id));
        Assert.Equal(
            AdmissionEffect.HumanGate,
            descriptors.Single(item => item.Id.Value == "SL-022").AdmissionEffect);
        Assert.All(
            descriptors.Where(item => item.Id.Value is not (
                "SL-007" or "SL-009" or "SL-014" or "SL-022" or "SL-023" or "SL-028")),
            item => Assert.Equal(AdmissionEffect.Block, item.AdmissionEffect));
        Assert.All(
            descriptors.Where(item => item.Id.Value is "SL-023" or "SL-028"),
            item => Assert.Equal(AdmissionEffect.Observe, item.AdmissionEffect));
        Assert.All(
            descriptors.Where(item => item.Id.Value is "SL-007" or "SL-009" or "SL-013" or "SL-014"),
            item => Assert.Equal(RuleLifecycle.Deferred, item.Lifecycle));
    }

    private static void AssertExactSl022Diagnostic(string protectedPath)
    {
        var verification = Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(
            BootstrapGate.Evaluate(RawChangeSet.Create([protectedPath])));

        var diagnostic = Assert.Single(BootstrapGate.CreateSl022Diagnostics(verification.ChangeSet));
        Assert.Equal("SL-022", diagnostic.RuleId.Value);
        Assert.Equal(protectedPath, diagnostic.Path);
    }
}
