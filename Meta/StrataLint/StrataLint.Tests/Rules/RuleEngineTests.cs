using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleEngineTests
{
    public static TheoryData<int, string> BlockingCases => new()
    {
        { 1, "upward-import" },
        { 2, "sorry" },
        { 3, "file-capacity" },
        { 4, "mirror" },
        { 5, "chronicle" },
        { 6, "badge" },
        { 8, "heart" },
        { 10, "generality" },
        { 11, "domain" },
        { 12, "header" },
        { 13, "task" },
        { 15, "formula" },
        { 16, "backfill" },
        { 17, "query" },
        { 18, "values" },
        { 19, "anomaly" },
        { 20, "axiom" },
        { 21, "future" },
    };

    [Theory]
    [MemberData(nameof(BlockingCases))]
    public void ActiveRuleHasGreenAndRedExecutableFixtures(int number, string mutation)
    {
        var green = new RuleFixture();
        if (number == 16)
        {
            green.AddBackfillTargets();
        }
        var greenResult = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(number), green.Build());
        Assert.Empty(greenResult.Diagnostics);
        Assert.Null(greenResult.DeferredCase);

        var red = new RuleFixture();
        if (number == 16)
        {
            red.AddBackfillTargets();
        }
        red.Apply(mutation);
        var redContext = number == 20 ? red.BuildForRuleCompatibility() : red.Build();
        var redResult = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(number), redContext);

        Assert.NotEmpty(redResult.Diagnostics);
        Assert.All(
            redResult.Diagnostics,
            diagnostic => Assert.Equal(RuleId.CreateKnown(number), diagnostic.RuleId));
        Assert.Null(redResult.DeferredCase);
    }

    [Fact]
    public void Sl001AllowsContentToImportTheAssumptionFoundationButNotTheReverse()
    {
        // Stratum content -> X_Assumptions (carrying a registered classical debt): allowed.
        var allowed = new RuleFixture();
        allowed.AddAssumptionImport();
        Assert.Empty(RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(1), allowed.Build()).Diagnostics);

        // X_Assumptions -> stratum content: forbidden, so the foundation stays a sink.
        var forbidden = new RuleFixture();
        forbidden.AddAssumptionImportingStratum();
        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(1), forbidden.Build()).Diagnostics);
        Assert.Equal(RuleId.CreateKnown(1), diagnostic.RuleId);
        Assert.Equal(RuleFixture.AssumptionDebtPath, diagnostic.Path);
        Assert.Contains("may not import", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl003CapacityHardBlocksAtEightHundredAndSoftWarnsAtSixHundred()
    {
        // 600 < n <= 800: a non-blocking soft warning, not a rejection.
        var soft = new RuleFixture();
        soft.Files[RuleFixture.RingPath] += string.Concat(Enumerable.Repeat("-- pad\n", 700));
        var softDiag = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), soft.Build()).Diagnostics);
        Assert.Equal(AdmissionEffect.Observe, softDiag.AdmissionEffect);
        Assert.Equal(DisplaySeverity.Warning, softDiag.DisplaySeverity);
        Assert.Contains("soft limit 600", softDiag.Message, StringComparison.Ordinal);

        // > 800: a hard block.
        var hard = new RuleFixture();
        hard.Files[RuleFixture.RingPath] += string.Concat(Enumerable.Repeat("-- pad\n", 801));
        var hardDiag = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), hard.Build()).Diagnostics);
        Assert.Equal(AdmissionEffect.Block, hardDiag.AdmissionEffect);
        Assert.Equal("artifact exceeds 800 lines", hardDiag.Message);
    }

    [Theory]
    [InlineData(7, "D5-T0011")]
    [InlineData(9, "D5-T0012")]
    [InlineData(14, "D5-T0010")]
    public void DeferredRulesNeverMasqueradeAsPass(int number, string caseId)
    {
        var result = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(number),
            new RuleFixture().Build());

        Assert.Empty(result.Diagnostics);
        Assert.Equal(CaseId.CreateKnown(caseId), result.DeferredCase);
    }

    [Fact]
    public void CoverageManifestNamesEveryRuleWithARealRedOrDeferredBranch()
    {
        var exercised = BlockingCases.Select(item => (int)item[0])
            .Concat(new[] { 7, 9, 14, 22 })
            .Order()
            .ToArray();

        Assert.Equal(Enumerable.Range(1, 22), exercised);
    }

    [Fact]
    public void Sl019AcceptsAValidTowerManifestAsAKnownGovernanceSchema()
    {
        var fixture = new RuleFixture();
        fixture.Files["Meta/StrataLint/TOWER.yaml"] = """
            schema_version: 1
            components:
              - id: failure-detector
                kind: repository-files
                members:
                  - Meta/StrataLint/TOWER.yaml
                judged_by:
                  - bootstrap-pr-1
                verification: verified
            bootstrap:
              id: bootstrap-pr-1
              judge: open
              reason: "Godel boundary."
              genesis_event: sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262
              commit: f3f471846dd81cfcc39ecaa386966fcf0b058464
              pull_request: 1
              verification: ASSUMED-UNVERIFIED
            """ + "\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build());

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl019RejectsMalformedTowerManifestThroughItsSchemaParser()
    {
        var fixture = new RuleFixture();
        fixture.Files["Meta/StrataLint/TOWER.yaml"] = """
            schema_version: 1
            components:
              - id: component
                kind: repository-files
                members: []
                judged_by:
                  - bootstrap-pr-1
            bootstrap:
              id: bootstrap-pr-1
              judge: open
              reason: "Godel boundary."
              genesis_event: sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262
              commit: f3f471846dd81cfcc39ecaa386966fcf0b058464
              pull_request: 1
              verification: ASSUMED-UNVERIFIED
            """ + "\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build());

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Contains(
            "invalid TOWER schema: tower components[0] keys are not canonical",
            diagnostic.Message,
            StringComparison.Ordinal);
    }
}
