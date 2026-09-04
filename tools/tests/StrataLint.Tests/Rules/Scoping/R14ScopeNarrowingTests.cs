using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class R14ScopeNarrowingTests
{
    private const string UnrelatedPath = "notes/unrelated.txt";
    private const string RuleImplementationPath =
        "tools/StrataLint.Engine/Rules/RepositoryRules.Content.cs";
    private const string DuplicateMessage = "duplicate GID";
    private const string EvidenceCollisionMessage =
        "evidence selector has multiple artifact kinds";

    [Fact]
    [BaseFactScopeProbe(
        15,
        typeof(RepositoryPathPolicy),
        nameof(RepositoryPathPolicy.EvaluateCompositionFindings))]
    public void Sl015EvaluateCompositionFindingsScopesCompositionParticipants() =>
        Sl015AdditionalEdgeScopeTests.RunEvaluateCompositionFindingsScopeProbe();

    [Fact]
    [BaseFactScopeProbe(
        15,
        typeof(RepositoryRules),
        nameof(RepositoryRules.DuplicateGidCollisions))]
    public void Sl015DuplicateGidCollisionsSuppressesHistoricalCollisionButKeepsImplementationRecheck()
    {
        var unrelated = DuplicateGidHistory();
        SetDelta(unrelated, UnrelatedPath, "base\n", "candidate\n");
        Assert.Equal(0, CountFindings(Execute(unrelated, UnrelatedPath), 15, DuplicateMessage));

        var implementation = DuplicateGidHistory();
        Assert.Equal(
            2,
            CountFindings(Execute(implementation, RuleImplementationPath), 15, DuplicateMessage));

        var baselineCollision = new RuleFixture();
        baselineCollision.Files[RuleFixture.BlueprintPath] = baselineCollision.Files[RuleFixture.RingPath];
        Assert.Equal(
            2,
            CountFindings(Execute(baselineCollision, RuleFixture.BlueprintPath), 15, DuplicateMessage));

        const string firstPath = "Blueprint/D5/S0/Carrier/First.md";
        const string secondPath = "Blueprint/D5/S0/Carrier/Second.md";
        var deltaCollision = new RuleFixture();
        deltaCollision.Files[firstPath] = Header("D5/B/S0/Carrier/DeltaCollision");
        deltaCollision.Files[secondPath] = Header("D5/B/S0/Carrier/DeltaCollision");
        Assert.Equal(
            2,
            CountFindings(Execute(deltaCollision, firstPath, secondPath), 15, DuplicateMessage));
    }

    [Fact]
    [BaseFactScopeProbe(
        15,
        typeof(RepositoryRules),
        nameof(RepositoryRules.EvidenceSelectorCollisions))]
    public void Sl015EvidenceSelectorCollisionsSuppressesHistoryButKeepsImplementationRecheck()
    {
        var unrelated = EvidenceCollisionHistory();
        SetDelta(unrelated, UnrelatedPath, "base\n", "candidate\n");
        Assert.Equal(
            0,
            CountFindings(Execute(unrelated, UnrelatedPath), 15, EvidenceCollisionMessage));

        var implementation = EvidenceCollisionHistory();
        Assert.Equal(
            2,
            CountFindings(
                Execute(implementation, RuleImplementationPath),
                15,
                EvidenceCollisionMessage));

        const string jsonPath = "Evidence/D5/S0/Carrier/Probe.result.json";
        const string yamlPath = "Evidence/D5/S0/Carrier/Probe.result.yaml";
        var baselineCollision = new RuleFixture();
        SetHistorical(baselineCollision, yamlPath, "value: baseline\n");
        baselineCollision.Files[jsonPath] = "{}\n";
        Assert.Equal(
            2,
            CountFindings(Execute(baselineCollision, jsonPath), 15, EvidenceCollisionMessage));

        var deltaCollision = new RuleFixture();
        deltaCollision.Files[jsonPath] = "{}\n";
        deltaCollision.Files[yamlPath] = "value: candidate\n";
        Assert.Equal(
            2,
            CountFindings(Execute(deltaCollision, jsonPath, yamlPath), 15, EvidenceCollisionMessage));
    }

    [Fact]
    public void Sl015EvidenceCollisionReportsDeltaAgainstBaselineCollision()
    {
        const string jsonPath = "Evidence/D5/S0/Carrier/Probe.result.json";
        const string yamlPath = "Evidence/D5/S0/Carrier/Probe.result.yaml";
        var fixture = new RuleFixture();
        SetHistorical(fixture, yamlPath, "value: baseline\n");
        fixture.Files[jsonPath] = "{}\n";

        Assert.Equal(
            2,
            CountFindings(Execute(fixture, jsonPath), 15, EvidenceCollisionMessage));
    }

    [Fact]
    public void Sl015EvidenceCollisionReportsDeltaAgainstDeltaCollision()
    {
        const string jsonPath = "Evidence/D5/S0/Carrier/Probe.result.json";
        const string yamlPath = "Evidence/D5/S0/Carrier/Probe.result.yaml";
        var fixture = new RuleFixture();
        fixture.Files[jsonPath] = "{}\n";
        fixture.Files[yamlPath] = "value: candidate\n";

        Assert.Equal(
            2,
            CountFindings(Execute(fixture, jsonPath, yamlPath), 15, EvidenceCollisionMessage));
    }

    [Fact]
    [BaseFactScopeProbe(
        15,
        typeof(RepositoryRules),
        nameof(RepositoryRules.HeaderAnchorCanonicality))]
    public void Sl015HeaderAnchorCanonicalityScopesHistoryAndKeepsDeltaAndImplementationRechecks()
    {
        const string path = "Blueprint/D5/S0/Carrier/AnchorProbe.md";
        const string message = "is not a canonical external anchor";

        var unrelated = new RuleFixture();
        SetHistorical(unrelated, path, Header("D5/B/S0/Carrier/AnchorProbe", "https://invalid"));
        SetDelta(unrelated, UnrelatedPath, "base\n", "candidate\n");
        Assert.Equal(0, CountFindings(Execute(unrelated, UnrelatedPath), 15, message));

        var changed = new RuleFixture();
        changed.Baseline[path] = Header("D5/B/S0/Carrier/AnchorProbe");
        changed.ForkPoint[path] = changed.Baseline[path];
        changed.Files[path] = Header("D5/B/S0/Carrier/AnchorProbe", "https://invalid");
        Assert.Equal(1, CountFindings(Execute(changed, path), 15, message));

        var implementation = new RuleFixture();
        SetHistorical(
            implementation,
            path,
            Header("D5/B/S0/Carrier/AnchorProbe", "https://invalid"));
        Assert.Equal(
            1,
            CountFindings(Execute(implementation, RuleImplementationPath), 15, message));
    }

    [Fact]
    [BaseFactScopeProbe(6)]
    public void Sl006BadgeScopesHistoryAndKeepsDeltaAndImplementationRechecks()
    {
        const string badgePath = "Library/historical-status.md";
        const string unrelatedStatusPath = "Library/unrelated.md";
        const string message = "hand-written status badge is forbidden";

        var unrelated = BadgeHistory(badgePath);
        SetDelta(unrelated, unrelatedStatusPath, "base\n", "candidate\n");
        Assert.Equal(0, CountFindings(Execute(unrelated, unrelatedStatusPath), 6, message));

        var changed = new RuleFixture();
        SetDelta(changed, badgePath, "plain text\n", "status: proven\n");
        Assert.Equal(1, CountFindings(Execute(changed, badgePath), 6, message));

        var implementation = BadgeHistory(badgePath);
        Assert.Equal(
            1,
            CountFindings(Execute(implementation, RuleImplementationPath), 6, message));
    }

    [Fact]
    [BaseFactScopeProbe(12)]
    public void Sl012LeanHeaderScopesHistoryAndKeepsDeltaAndImplementationRechecks()
    {
        const string malformed = "def goldenRing : Nat := 0\n";
        const string message = "expected the exact six-line header at byte zero";

        var unrelated = new RuleFixture();
        SetHistorical(unrelated, RuleFixture.RingPath, malformed);
        unrelated.Files[RuleFixture.ValuesBindingPath] += "-- candidate delta\n";
        Assert.Equal(
            0,
            CountFindings(Execute(unrelated, RuleFixture.ValuesBindingPath), 12, message));

        var changed = new RuleFixture();
        changed.Files[RuleFixture.RingPath] = malformed;
        Assert.Equal(1, CountFindings(Execute(changed, RuleFixture.RingPath), 12, message));

        var implementation = new RuleFixture();
        SetHistorical(implementation, RuleFixture.RingPath, malformed);
        Assert.Equal(
            1,
            CountFindings(Execute(implementation, RuleImplementationPath), 12, message));
    }

    [Fact]
    [BaseFactScopeProbe(25)]
    public void Sl025BlueprintStemScopesHistoryAndKeepsImplementationRecheck()
    {
        const string orphanPath = "Blueprint/D5/S0/Carrier/HistoricalOrphan.md";
        const string message = "Blueprint markdown has no matching .scribe.cs source";

        var unrelated = new RuleFixture();
        SetHistorical(unrelated, orphanPath, "# historical orphan\n");
        unrelated.Files[RuleFixture.BlueprintPath] += "candidate delta\n";
        Assert.Equal(
            0,
            CountFindings(Execute(unrelated, RuleFixture.BlueprintPath), 25, message, orphanPath));

        var implementation = new RuleFixture();
        SetHistorical(implementation, orphanPath, "# historical orphan\n");
        Assert.Equal(
            1,
            CountFindings(
                Execute(implementation, RuleImplementationPath),
                25,
                message,
                orphanPath));
    }

    [Theory]
    [InlineData(
        RuleFixture.BlueprintSourcePath,
        RuleFixture.BlueprintPath,
        "Blueprint markdown has no matching .scribe.cs source")]
    [InlineData(
        RuleFixture.BlueprintPath,
        RuleFixture.BlueprintSourcePath,
        "Blueprint Scribe source has no matching .md projection")]
    public void Sl025BlueprintStemReportsDeletionOfEitherPairEndpoint(
        string deletedPath,
        string findingPath,
        string message)
    {
        var fixture = new RuleFixture();
        fixture.Files.Remove(deletedPath);

        Assert.Equal(
            1,
            CountFindings(Execute(fixture, deletedPath), 25, message, findingPath));
    }

    private static RuleFixture DuplicateGidHistory()
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, RuleFixture.BlueprintPath, fixture.Files[RuleFixture.RingPath]);
        return fixture;
    }

    private static RuleFixture EvidenceCollisionHistory()
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, "Evidence/D5/S0/Carrier/Probe.result.json", "{}\n");
        SetHistorical(fixture, "Evidence/D5/S0/Carrier/Probe.result.yaml", "value: history\n");
        return fixture;
    }

    private static RuleFixture BadgeHistory(string path)
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, path, "status: proven\n");
        return fixture;
    }

    private static CompletedRuleSet Execute(RuleFixture fixture, params string[] changedPaths) =>
        Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(
                fixture.BuildScopeProbe(RawChangeSet.Create(changedPaths)))).Capability;

    private static int CountFindings(
        CompletedRuleSet completed,
        int ruleNumber,
        string message,
        string? path = null) =>
        completed.Diagnostics.Count(diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(ruleNumber)
            && diagnostic.Message.Contains(message, StringComparison.Ordinal)
            && (path is null || diagnostic.Path == path));

    private static void SetHistorical(RuleFixture fixture, string path, string text)
    {
        fixture.Files[path] = text;
        fixture.Baseline[path] = text;
        fixture.ForkPoint[path] = text;
    }

    private static void SetDelta(RuleFixture fixture, string path, string baseline, string current)
    {
        fixture.Baseline[path] = baseline;
        fixture.ForkPoint[path] = baseline;
        fixture.Files[path] = current;
    }

    private static string Header(string gid, string anchors = "") => $"""
        /- GID: {gid}
           generality: G
           mirror-B: none(waiver:test-fixture)
           mirror-E: none(waiver:test-fixture)
           anchors: [{anchors}]
           digest: R14 scope fixture. -/
        """;
}
