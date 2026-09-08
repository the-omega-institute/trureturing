using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.UtilityAdmissionTestSupport;

namespace StrataLint.Tests;

public sealed class OrdinaryInstanceAdmissionTests
{
    private const string Ordinary =
        "kind=certified-instance; basis=terminal=gid:D5/S0/Carrier/Ring.fixed_sum";

    [Theory]
    [InlineData("certified-instance", "ChangedContent")]
    [InlineData("bounded-enumeration", "ChangedContent")]
    [InlineData("certified-instance", "PreDeposit")]
    [InlineData("bounded-enumeration", "PreDeposit")]
    [InlineData("certified-instance", "FirstFreeze")]
    [InlineData("bounded-enumeration", "FirstFreeze")]
    public void OrdinaryKindsHaveNoConsumerOrTerminalException(string kind, string phase)
    {
        var fixture = InstanceFixture("none");
        var context = fixture.Build(RawChangeSet.Create([]));
        foreach (var basis in new[] { "consumer=D5/S0/Carrier/Ring.fixed_sum",
            "terminal=gid:D5/S0/Carrier/Ring.fixed_sum", "terminal=task:D5-T0001",
            "terminal=atom:" + RuleFixture.FixtureAtomId })
        foreach (var extra in new[] { "", "; result=D5/S0/Carrier/Ring.fixed_sum" })
        {
            var validation = UtilityDeclarationValidator.Validate(Enum.Parse<UtilityValidationPhase>(phase),
                RepoPath.CreateKnown(RuleFixture.RingPath), $"kind={kind}; basis={basis}{extra}",
                context.Current, () => context.Lean.Report);
            Assert.Equal(UtilityValidationFailure.OrdinaryInstanceForbidden, validation.Failure);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void OrdinaryPositiveInstanceIsBlockedByFullCatalogWithOrWithoutFreeze(bool freeze)
    {
        var fixture = InstanceFixture(Ordinary);
        var changes = new List<(string, RawChangeKind)> { (RuleFixture.RingPath, RawChangeKind.Added) };
        if (freeze) changes.Add((AddCandidateState(fixture), RawChangeKind.Added));

        var result = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.CreateWithKinds(changes))));

        Assert.Contains(result.Capability.Diagnostics, IsOrdinaryBan);
        Assert.Single(result.Capability.Diagnostics, diagnostic => diagnostic.RuleId == UtilityRuleId
            && diagnostic.Message.StartsWith("UTILITY-OBSERVED ", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData(RawChangeKind.Added)]
    [InlineData(RawChangeKind.Modified)]
    [InlineData(RawChangeKind.Copied)]
    public void PresentChangedDestinationIsSelectedRegardlessOfChangeKind(RawChangeKind kind)
    {
        var fixture = InstanceFixture(Ordinary);
        var context = fixture.Build(RawChangeSet.CreateWithKinds([(RuleFixture.RingPath, kind)]));

        Assert.True(UtilityAdmissionRule.IsAffectedBy(context));
        Assert.Contains(RuleCatalog.Default.EvaluateSingle(UtilityRuleId, context).Diagnostics, IsOrdinaryBan);
    }

    [Theory]
    [InlineData(RawChangeKind.Added)]
    [InlineData(RawChangeKind.Modified)]
    public void FirstStateOnlyAdmissionIsSelectedRegardlessOfChangeKind(RawChangeKind kind)
    {
        var fixture = InstanceFixture(Ordinary);
        fixture.Baseline[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath];
        var state = AddCandidateState(fixture);
        var context = fixture.Build(RawChangeSet.CreateWithKinds([(state, kind)]));

        Assert.True(UtilityAdmissionRule.IsAffectedBy(context));
        Assert.Contains(RuleCatalog.Default.EvaluateSingle(UtilityRuleId, context).Diagnostics, IsOrdinaryBan);
    }

    [Fact]
    public void BodyOnlyChangeRechecksUnfrozenOrdinaryClassification()
    {
        var fixture = InstanceFixture(Ordinary);
        fixture.Baseline[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath]
            .Replace("17 + 4 = 21", "19 + 4 = 23", StringComparison.Ordinal);
        Assert.Contains(EvaluateChanged(fixture), IsOrdinaryBan);
    }

    [Fact]
    public void CandidateOnlyStateCannotExemptChangedContent()
    {
        var fixture = InstanceFixture(Ordinary);
        AddCandidateState(fixture);
        Assert.Contains(EvaluateChanged(fixture), IsOrdinaryBan);
    }

    [Theory]
    [InlineData(null)]
    [InlineData("malformed")]
    public void MissingOrMalformedUtilityOnSourceOnlyAdmissionBlocks(string? utility)
    {
        var fixture = InstanceFixture(utility);
        Assert.Contains(EvaluateChanged(fixture), diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Block
            && diagnostic.Message.Contains(utility is null ? "UTILITY-MISSING" : "UTILITY-SYNTAX", StringComparison.Ordinal));
    }

    [Fact]
    public void MissingHeaderCannotSuppressSourceOnlySelection()
    {
        var fixture = InstanceFixture(null);
        fixture.Files[RuleFixture.RingPath] = "theorem fixed_sum : 17 + 4 = 21 := rfl\n";
        Assert.Contains(EvaluateChanged(fixture), diagnostic => diagnostic.Message.StartsWith("UTILITY-MISSING", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("none")]
    [InlineData("kind=checker; basis=terminal=gid:D5/S0/Carrier/Ring.fixed_sum; instance=D5/S0/Carrier/Ring.fixed_sum")]
    public void OnlyRelabelingAnOrdinaryBodyIsBlockedAndObserved(string newUtility)
    {
        var fixture = InstanceFixture(Ordinary);
        fixture.Baseline[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath];
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath].Replace(Ordinary, newUtility, StringComparison.Ordinal);

        var diagnostics = EvaluateChanged(fixture);

        Assert.Contains(diagnostics, diagnostic => diagnostic.Message.StartsWith("UTILITY-CLASSIFICATION-CHANGED", StringComparison.Ordinal)
            && diagnostic.AdmissionEffect is AdmissionEffect.Observe);
        Assert.Contains(diagnostics, diagnostic => diagnostic.Message.StartsWith("UTILITY-CLASSIFICATION-DOWNGRADE", StringComparison.Ordinal)
            && diagnostic.AdmissionEffect is AdmissionEffect.Block);
    }

    [Fact]
    public void RealBodyChangeToNoneIsObservedWithoutClaimingGenerality()
    {
        var fixture = InstanceFixture(Ordinary);
        fixture.Baseline[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath];
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath]
            .Replace(Ordinary, "none", StringComparison.Ordinal)
            .Replace("fixed_sum : 17 + 4 = 21", "fixed_sum (n : Nat) : n + 0 = n", StringComparison.Ordinal);

        var diagnostics = EvaluateChanged(fixture);

        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(diagnostics, diagnostic => diagnostic.Message.StartsWith("UTILITY-CLASSIFICATION-CHANGED", StringComparison.Ordinal));
        Assert.Contains(diagnostics, diagnostic => diagnostic.Message.Contains("semantics=unverified-by-machine", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("malformed", "unparsed")]
    [InlineData(null, "missing")]
    public void RemovingOrBreakingClassificationIsObservedAndBlocked(string? replacement, string display)
    {
        var fixture = InstanceFixture(Ordinary);
        fixture.Baseline[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath];
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath]
            .Replace("   utility: " + Ordinary + "\n", replacement is null ? "" : "   utility: " + replacement + "\n", StringComparison.Ordinal);

        var diagnostics = EvaluateChanged(fixture);

        Assert.Contains(diagnostics, item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(diagnostics, item => item.Message.StartsWith("UTILITY-CLASSIFICATION-CHANGED", StringComparison.Ordinal)
            && item.Message.Contains("after=" + display, StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("G", false)]
    [InlineData("I", false)]
    [InlineData("I", true)]
    public void GeneralContentRemainsAcceptedIndependentlyOfGeneralityLabel(string generality, bool numeric)
    {
        const string result = "D5/S0/Carrier/Ring.fixed_sum";
        var fixture = InstanceFixture(numeric
            ? $"kind=numeric-reduction; basis=consumer={result}; premises={result}"
            : "none");
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath]
            .Replace("generality: I", "generality: " + generality, StringComparison.Ordinal)
            .Replace("fixed_sum : 17 + 4 = 21", "fixed_sum (n : Nat) : n + 0 = n", StringComparison.Ordinal);
        fixture.Reports[RuleFixture.RingPath] = new([], [new("fixed_sum", "theorem", "forall n : Nat, n + 0 = n", [])]);

        Assert.DoesNotContain(EvaluateChanged(fixture), item => item.AdmissionEffect is AdmissionEffect.Block);
    }

    [Fact]
    public void UnchangedHistoricalSourceAndJudgeOnlyChangesDoNotSweepUtility()
    {
        var fixture = InstanceFixture(null);
        fixture.Baseline[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath];
        Assert.Empty(EvaluateChanged(fixture));
        const string judge = "tools/StrataLint.Engine/Rules/TheoryGeneration/UtilityAdmissionRule.cs";
        fixture.Files[judge] = "// changed judge\n";
        Assert.Empty(RuleCatalog.Default.EvaluateSingle(UtilityRuleId,
            fixture.Build(RawChangeSet.Create([judge]))).Diagnostics);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CurrentOnlyStateDoesNotBypassProductionDepositPrecheck(bool currentPin)
    {
        var fixture = InstanceFixture(Ordinary);
        if (currentPin) AddCandidateState(fixture);
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([RuleFixture.RingPath]),
            Raw(fixture.Files), Raw(fixture.Baseline));
        var console = new BufferedConsole();

        var exit = CliApplication.Run(["deposit-header-check", "--target", RuleFixture.RingPath,
                "--protected-base", new string('b', 40)],
            new ProductionCliEnvironment("/repo", repository, new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports))), console);

        Assert.Equal(1, exit);
        Assert.Contains("DEPOSIT_HEADER_UTILITY_ORDINARY_INSTANCE_BANNED", console.Output, StringComparison.Ordinal);
        Assert.Equal(["baseline"], repository.ReadRevisionCalls);
    }

    [Theory]
    [InlineData("ChangedContent")]
    [InlineData("PreDeposit")]
    [InlineData("FirstFreeze")]
    public void NoneStillRequiresCurrentNonerroredModuleReport(string phase)
    {
        var fixture = InstanceFixture("none");
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.RingPath]));
        foreach (var report in new[] {
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()),
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> {
                [RuleFixture.RingPath] = new([], [], Error: "elaboration failed") }) })
        {
            var validation = UtilityDeclarationValidator.Validate(Enum.Parse<UtilityValidationPhase>(phase), RepoPath.CreateKnown(RuleFixture.RingPath),
                "none", context.Current, () => report);
            Assert.Equal(UtilityValidationFailure.InputUnknown, validation.Failure);
        }
    }

    internal static RuleFixture InstanceFixture(string? utility)
    {
        var fixture = new RuleFixture();
        fixture.Baseline.Remove(RuleFixture.RingPath);
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath]
            .Replace("generality: G", "generality: I", StringComparison.Ordinal)
            .Replace("def goldenRing : Nat := 0", "theorem fixed_sum : 17 + 4 = 21 := rfl", StringComparison.Ordinal);
        if (utility is not null) fixture.Files[RuleFixture.RingPath] = WithUtility(fixture.Files[RuleFixture.RingPath], utility);
        fixture.Reports[RuleFixture.RingPath] = new([], [new("fixed_sum", "theorem", "17 + 4 = 21", [])]);
        return fixture;
    }

    internal static string AddCandidateState(RuleFixture fixture)
    {
        var state = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(RuleFixture.RingPath)).Value;
        fixture.Files[state] = "{\"statement_id\":\"sha256:" + new string('0', 64) + "\"}\n";
        return state;
    }

    private static IReadOnlyList<Diagnostic> EvaluateChanged(RuleFixture fixture) =>
        RuleCatalog.Default.EvaluateSingle(UtilityRuleId,
            fixture.Build(RawChangeSet.Create([RuleFixture.RingPath]))).Diagnostics;

    private static bool IsOrdinaryBan(Diagnostic diagnostic) => diagnostic.RuleId == UtilityRuleId
        && diagnostic.AdmissionEffect is AdmissionEffect.Block
        && diagnostic.Message.StartsWith("UTILITY-ORDINARY-INSTANCE-BANNED", StringComparison.Ordinal);

    internal static RawRepositorySnapshot Raw(Dictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
}
