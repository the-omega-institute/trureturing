using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ActiveRuleScopeProbeTests
{
    private const string RuleImplementationPath =
        "tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs";

    [Fact]
    [BaseFactScopeProbe(8)]
    public void Sl008AuthorizationLedgerScopesHistoryAndKeepsDeltaAndImplementationRechecks()
    {
        const string path = HeartsAuthorizationLedger.Path;
        const string message = "exactly four columns";

        var unrelated = MalformedAuthorizationLedger();
        AssertNoFinding(
            Execute(unrelated, "Golden/Frozen/accepted/fixture-event.json"),
            8,
            message,
            path);

        AssertFinding(Execute(MalformedAuthorizationLedger(), path), 8, message, path);
        AssertFinding(
            Execute(
                MalformedAuthorizationLedger(),
                "tools/StrataLint.Engine/Authorization/HeartsAuthorizationLedger.cs"),
            8,
            message,
            path);
    }

    [Fact]
    [BaseFactScopeProbe(16)]
    public void Sl016SourceMetadataScopesHistoryAndKeepsImplementationDeltaOnly()
    {
        const string path = "Meta/Digestion/backfill/delta-v0.1/source.toml";
        const string message = "source metadata";

        AssertNoFinding(
            Execute(InvalidBackfillSourceHistory(), RuleFixture.BlueprintPath),
            16,
            message,
            BackfillInventoryLoader.RelativePath);
        AssertFinding(
            Execute(InvalidBackfillSourceHistory(), path),
            16,
            message,
            BackfillInventoryLoader.RelativePath);
        AssertNoFinding(
            Execute(
                InvalidBackfillSourceHistory(),
                "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs"),
            16,
            message,
            BackfillInventoryLoader.RelativePath);
    }

    [Fact]
    [BaseFactScopeProbe(21)]
    public void Sl021InstantiationScopesHistoricalTheoryPathsAndKeepsImplementationRecheck()
    {
        const string historicalPath = "D8/S0/Carrier/Historical.lean";
        const string unrelatedPath = "D9/S0/Carrier/Delta.lean";
        const string message = "未实例化";

        var unrelated = InstantiationHistory(historicalPath);
        SetHistorical(unrelated, unrelatedPath, "future delta\n");
        AssertNoFinding(Execute(unrelated, unrelatedPath), 21, message, historicalPath);

        AssertFinding(
            Execute(InstantiationHistory(historicalPath), historicalPath),
            21,
            message,
            historicalPath);
        AssertFinding(
            Execute(InstantiationHistory(historicalPath), RuleImplementationPath),
            21,
            message,
            historicalPath);
    }

    [Fact]
    [BaseFactScopeProbe(23)]
    public void Sl023DescribeLatexScopesHistoricalDefinitionAndKeepsImplementationRecheck()
    {
        const string path = "Blueprint/D5/S3/Weil/Historical.scribe.cs";
        const string unrelatedPath = "Blueprint/D5/S3/Weil/Delta.scribe.cs";
        const string message = "must be Lean-derived";
        var emissions = HandAuthoredTheorem(path);

        var unrelated = new RuleFixture();
        SetHistorical(unrelated, path, "// historical\n");
        SetHistorical(unrelated, unrelatedPath, "// baseline\n");
        unrelated.Files[unrelatedPath] = "// candidate\n";
        AssertNoFinding(Execute(unrelated, unrelatedPath, emissions), 23, message, path);

        var changed = new RuleFixture();
        SetHistorical(changed, path, "// historical\n");
        AssertFinding(Execute(changed, path, emissions), 23, message, path);

        var implementation = new RuleFixture();
        SetHistorical(implementation, path, "// historical\n");
        AssertFinding(
            Execute(
                implementation,
                "tools/StrataLint.Scribe/Reporting/ScribeReport.cs",
                emissions),
            23,
            message,
            path);
    }

    [Fact]
    [BaseFactScopeProbe(26)]
    public void Sl026LegacyConstructorScopesHistoryAndKeepsDeltaAndImplementationRechecks()
    {
        const string path = "Blueprint/D5/S0/Carrier/HistoricalLegacy.scribe.cs";
        const string unrelatedPath = "Blueprint/D5/S0/Carrier/DeltaClean.scribe.cs";
        const string message = "legacy Scribe constructor";

        var unrelated = LegacyScribeHistory(path);
        SetHistorical(unrelated, unrelatedPath, "// baseline\n");
        unrelated.Files[unrelatedPath] = "// candidate\n";
        AssertNoFinding(Execute(unrelated, unrelatedPath), 26, message, path);

        AssertFinding(Execute(LegacyScribeHistory(path), path), 26, message, path);
        AssertFinding(
            Execute(
                LegacyScribeHistory(path),
                "tools/StrataLint.Engine/Rules/ScribeBudget/RepositoryRules.ScribeBudget.cs"),
            26,
            message,
            path);
    }

    [Fact]
    [BaseFactScopeProbe(28)]
    public void Sl028DuplicateStatementScopesHistoryAndKeepsDeltaAndImplementationRechecks()
    {
        var unrelated = DuplicateStatementPair(touchRight: false);
        unrelated.AddStatementModule(
            "D5/S3/Weil/DeltaDistinct",
            "D5.S3.Weil.DeltaDistinct.unrelated",
            RuleFixture.DistinctStatementType,
            touched: true);
        Assert.Empty(EvaluateSingle(unrelated, 28).Diagnostics);

        Assert.Single(EvaluateSingle(DuplicateStatementPair(touchRight: true), 28).Diagnostics);

        var implementation = DuplicateStatementPair(touchRight: false);
        Assert.Single(EvaluateSingle(implementation, 28, RuleImplementationPath).Diagnostics);
    }

    private static RuleFixture MalformedAuthorizationLedger()
    {
        var fixture = new RuleFixture();
        SetHistorical(
            fixture,
            HeartsAuthorizationLedger.Path,
            HeartsAuthorizationLedger.Header + "not a ledger row\n");
        return fixture;
    }

    private static RuleFixture InvalidBackfillSourceHistory()
    {
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        const string path = "Meta/Digestion/backfill/delta-v0.1/source.toml";
        fixture.Files[path] += "\n";
        return fixture;
    }

    private static RuleFixture InstantiationHistory(string path)
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, path, "future history\n");
        return fixture;
    }

    private static VerifiedScribeEmissions HandAuthoredTheorem(string path) =>
        VerifiedScribeEmissions.Create(
            [],
            [],
            [
                new ScribeDescribeLatexRecord(
                    "D5/S3/Weil/Historical#describe/statement",
                    path,
                    Kind: "theorem",
                    HasValidLatex: true,
                    FormulaProvenance: "hand-authored",
                    ProjectionFailureReason: null),
            ]);

    private static RuleFixture LegacyScribeHistory(string path)
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, path, "DefinitionDsl.LeanTheorem(x);\n");
        return fixture;
    }

    private static RuleFixture DuplicateStatementPair(bool touchRight)
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.channel_monotone",
            RuleFixture.DuplicateStatementType);
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.dpi_defect",
            RuleFixture.DuplicateStatementType,
            touched: touchRight);
        return fixture;
    }

    private static SingleRuleEvaluation EvaluateSingle(
        RuleFixture fixture,
        int ruleNumber,
        string? changedPath = null)
    {
        var changes = changedPath is null
            ? RawChangeSet.Create(fixture.Changes)
            : RawChangeSet.Create([changedPath]);
        return RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(ruleNumber),
            fixture.Build(changes));
    }

    private static void SetHistorical(RuleFixture fixture, string path, string text)
    {
        fixture.Files[path] = text;
        fixture.Baseline[path] = text;
        fixture.ForkPoint[path] = text;
    }

    private static CompletedRuleSet Execute(
        RuleFixture fixture,
        string changedPath,
        VerifiedScribeEmissions? emissions = null) =>
        Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(
                fixture.Build(RawChangeSet.Create([changedPath]), verifiedScribeEmissions: emissions)))
            .Capability;

    private static void AssertFinding(
        CompletedRuleSet completed,
        int ruleNumber,
        string message,
        string path) =>
        Assert.Contains(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(ruleNumber)
            && diagnostic.Path == path
            && diagnostic.Message.Contains(message, StringComparison.Ordinal));

    private static void AssertNoFinding(
        CompletedRuleSet completed,
        int ruleNumber,
        string message,
        string path) =>
        Assert.DoesNotContain(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(ruleNumber)
            && diagnostic.Path == path
            && diagnostic.Message.Contains(message, StringComparison.Ordinal));
}
