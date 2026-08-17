using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoristFrontierContractTests
{
    public static TheoryData<string> HistoricalCandidates => new()
    {
        "finite-depth-metric",
        "prime-norm-irreducibility",
    };

    public static TheoryData<string, string> ContractMutations => new()
    {
        { "missing-contract", "theorist contract is required" },
        { "duplicate-contract", "duplicate theorist contracts are forbidden" },
        { "missing-closing-marker", "contract closing marker is missing" },
        { "malformed-json", "contract is not valid JSON" },
        { "unknown-field", "contract keys are not canonical" },
        { "missing-field", "contract keys are not canonical" },
        { "duplicate-field", "contract keys are not canonical" },
        { "wrong-schema", "contract schema must be" },
        { "blank-falsifier", "falsifier must be non-empty" },
        { "wrong-statement-gid", "exact_statement.gid must select the open declaration" },
        { "unknown-statement-field", "exact_statement keys are not canonical" },
        { "wrong-statement-address", "exact_statement.statement_sha256 does not match" },
        { "closed-statement", "exact statement must be open via sorryAx" },
        { "excluded-statement", "exact statement must be open via sorryAx" },
        { "second-open-statement", "contract must bind the module's only open declaration" },
        { "empty-motivations", "motivation_gids must be a non-empty sorted unique string array" },
        { "duplicate-motivations", "motivation_gids must be a non-empty sorted unique string array" },
        { "unsorted-motivations", "motivation_gids must be a non-empty sorted unique string array" },
        { "bad-motivation-gid", "motivation_gids[0] is not a canonical formal GID" },
        { "bad-motivation-plane", "motivation_gids[0] is not a canonical formal GID" },
        { "unfrozen-motivation", "motivation_gids[0] is not an active frozen member" },
        { "empty-search-receipts", "search_receipt_gids must be a non-empty sorted unique string array" },
        { "duplicate-search-receipts", "search_receipt_gids must be a non-empty sorted unique string array" },
        { "bad-search-plane", "search_receipt_gids[0] must be a Library GID" },
        { "missing-search-receipt", "search_receipt_gids[0] does not resolve" },
        { "empty-computation-receipts", "computation_receipt_gids must be a non-empty sorted unique string array" },
        { "duplicate-computation-receipts", "computation_receipt_gids must be a non-empty sorted unique string array" },
        { "bad-computation-plane", "computation_receipt_gids[0] must be an Evidence GID" },
        { "missing-computation-receipt", "computation_receipt_gids[0] does not resolve" },
        { "unknown-triage", "triage_class must be one of theorem, window, wall" },
        { "claimed-truth-status", "contract keys are not canonical" },
    };

    [Theory]
    [MemberData(nameof(HistoricalCandidates))]
    public void HistoricalTheorySelfGrowthCandidateCarriesAValidOpenContract(string fixtureName)
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(fixtureName);
        var context = fixture.Build();
        var mission = MissionFileLoader.Load(context.Current);
        Assert.True(
            mission is MissionLoadOutcome.Loaded,
            mission is MissionLoadOutcome.Invalid invalid ? invalid.Error.Message : "unknown MISSION outcome");

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(2),
            context).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Theory]
    [MemberData(nameof(HistoricalCandidates))]
    public void HistoricalFixtureMatchesTheRecordedTheorySelfGrowthBlob(string fixtureName)
    {
        var (source, blobOid) = RuleFixture.HistoricalTheoristBlob(fixtureName);

        Assert.Equal(
            blobOid,
            FrozenContentAddress.ComputeGitBlobOid(
                Encoding.UTF8.GetBytes(source),
                HashAlgorithmName.SHA1));
    }

    [Theory]
    [MemberData(nameof(HistoricalCandidates))]
    public void HistoricalTheorySelfGrowthCandidateWithoutContractIsRejected(string fixtureName)
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(fixtureName, includeContract: false);

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("theorist contract is required", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(HistoricalCandidates))]
    public void HistoricalTheorySelfGrowthCandidateWithBrokenReferenceIsRejected(string fixtureName)
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(fixtureName);
        fixture.MutateTheoristTarget("unfrozen-motivation");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("is not an active frozen member", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(ContractMutations))]
    public void EveryTheoristContractGuardFailsClosed(string mutation, string expectedPredicate)
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget("prime-norm-irreducibility");
        fixture.MutateTheoristTarget(mutation);

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(expectedPredicate, diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingTypedOwnerIsUnknownRatherThanInferredFromTaskOrSorrySyntax()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            ownerKind: null,
            includeContract: false);

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("Frontier owner is unknown", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GovernanceOwnerDoesNotBecomeTheoryGenerationFromTaskOrSorrySyntax()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            ownerKind: "governance",
            includeContract: false);

        Assert.Empty(Evaluate(fixture));
    }

    [Fact]
    public void GovernanceOwnerCannotCarryATheoristContract()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            ownerKind: "governance");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "contract requires declaration-ready-mathematical-open ownership",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MathematicalNotYetStatedOwnerCannotCarryAnElaboratedOpenDeclaration()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            ownerKind: "mathematical-not-yet-stated",
            includeContract: false,
            baselineOwnerKind: "mathematical-not-yet-stated");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "mathematical-not-yet-stated owner cannot carry an elaborated sorryAx declaration",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void BaselineWithoutTheNewContractRemainsLoadableUntilTypedOwnerTransition()
    {
        var grandfathered = new RuleFixture();
        grandfathered.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            includeContract: false,
            baselineOwnerKind: "declaration-ready-mathematical-open");
        Assert.Empty(Evaluate(grandfathered));

        var transitioned = new RuleFixture();
        transitioned.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            includeContract: false,
            baselineOwnerKind: "governance");
        var diagnostic = Assert.Single(Evaluate(transitioned));
        Assert.Contains("theorist contract is required", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GrandfatheredModuleOptInIsValidatedInTheCandidateTree()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            baselineOwnerKind: "declaration-ready-mathematical-open");
        fixture.MutateTheoristTarget("wrong-statement-address");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "exact_statement.statement_sha256 does not match",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void UnreadableMissionReportsAnUndecidableOwnerRatherThanAnUnclassifiedModule()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget("prime-norm-irreducibility", includeContract: false);
        fixture.CorruptMission();

        var diagnostics = Evaluate(fixture);

        // Every new Frontier module loses its owner at once, so the whole set must say so.
        Assert.NotEmpty(diagnostics);
        Assert.All(diagnostics, diagnostic => Assert.Contains(
            "Frontier owner is undecidable because docs/MISSION.md does not load: "
            + "MISSION must contain exactly one mission-v1 fenced block",
            diagnostic.Message,
            StringComparison.Ordinal));
        Assert.Contains(
            diagnostics,
            diagnostic => diagnostic.Path == "D5/X_Frontier/PrimeNormIrreducibility.lean");
    }

    [Fact]
    public void UnreadableMissionDoesNotSilentlyAdmitAContractCarrier()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            baselineOwnerKind: "declaration-ready-mathematical-open");
        fixture.CorruptMission();

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "theorist contract ownership is undecidable because docs/MISSION.md does not load",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MigratedContractCannotBeDeletedAfterItEntersTheBaseline()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            includeContract: false,
            baselineOwnerKind: "declaration-ready-mathematical-open",
            baselineIncludeContract: true);

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("theorist contract is required", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DeletedBaselineContractCarrierIsRejectedWhenItsOwnerEntryIsAlsoDeleted()
    {
        var fixture = BaselineContractCarrier();
        fixture.DeleteTheoristTargetAndOwner();

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Equal("D5/X_Frontier/PrimeNormIrreducibility.lean", diagnostic.Path);
        Assert.Contains("theorist contract source is unavailable", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CurrentContractCarrierWithoutCompiledReportFailsClosed()
    {
        var fixture = BaselineContractCarrier();
        fixture.RemoveTheoristTargetReport();

        var diagnostic = Assert.Single(EvaluateForRuleCompatibility(fixture));

        Assert.Equal("D5/X_Frontier/PrimeNormIrreducibility.lean", diagnostic.Path);
        Assert.Contains("theorist contract compiled report is unavailable", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DeletedBaselineContractCarrierDefeatsTheEmptyCandidateReportEscape()
    {
        var fixture = BaselineContractCarrier();
        fixture.DeleteTheoristTargetAndOwner();
        fixture.RemoveCurrentFrontierReports();
        var context = fixture.BuildForRuleCompatibility();
        Assert.DoesNotContain(
            context.Lean.Report.Files.Keys,
            static path => path.Value.StartsWith("D5/X_Frontier/", StringComparison.Ordinal));

        var diagnostic = Assert.Single(EvaluateContext(context));

        Assert.Equal("D5/X_Frontier/PrimeNormIrreducibility.lean", diagnostic.Path);
        Assert.Contains("theorist contract source is unavailable", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DeletedLegacyBaselineModuleWithoutContractDoesNotEnterTheMigratedClass()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            baselineOwnerKind: "declaration-ready-mathematical-open");
        fixture.DeleteTheoristTargetAndOwner();

        Assert.Empty(Evaluate(fixture));
    }

    private static RuleFixture BaselineContractCarrier()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            baselineOwnerKind: "declaration-ready-mathematical-open",
            baselineIncludeContract: true);
        return fixture;
    }

    private static ImmutableArray<Diagnostic> Evaluate(RuleFixture fixture) =>
        EvaluateContext(fixture.Build());

    private static ImmutableArray<Diagnostic> EvaluateForRuleCompatibility(RuleFixture fixture) =>
        EvaluateContext(fixture.BuildForRuleCompatibility());

    private static ImmutableArray<Diagnostic> EvaluateContext(RuleEvaluationContext context) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(2), context).Diagnostics;
}
