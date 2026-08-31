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
        { 15, "formula" },
        { 16, "backfill" },
        { 17, "query" },
        { 18, "values" },
        { 19, "anomaly" },
        { 20, "axiom" },
        { 21, "future" },
        { 25, "blueprint-skeleton" },
        { 26, "legacy-scribe" },
    };

    public static TheoryData<int, string> AffectedInputs => new()
    {
        { 1, RuleFixture.RingPath },
        { 2, RuleFixture.RingPath },
        { 3, RuleFixture.RingPath },
        { 4, RuleFixture.BlueprintPath },
        { 5, "Chronicle/2026/07/10-old.md" },
        { 6, RuleFixture.BlueprintPath },
        { 8, RuleFixture.HeartsPath },
        { 10, RuleFixture.RingPath },
        { 11, RuleFixture.RingPath },
        { 12, RuleFixture.RingPath },
        { 15, "notes/new-artifact.txt" },
        { 16, RuleFixture.FixtureBackfillSourcePath },
        { 17, "Library/queries.yaml" },
        { 18, ValuesKernelBindingValidator.RelativePath },
        { 18, "Directory.Build.props" },
        { 19, "Evidence/D5/S0/Carrier/Result.run.json" },
        { 20, RuleFixture.RingPath },
        { 21, "D8/S0/Carrier/Ring.lean" },
        { 22, RuleFixture.SyntheticProtectedPath },
        { 23, RuleFixture.BlueprintSourcePath },
        { 23, "Directory.Build.props" },
        { 25, RuleFixture.BlueprintPath },
        { 26, RuleFixture.BlueprintSourcePath },
    };

    public static TheoryData<int, string?> UnaffectedInputs => new()
    {
        { 1, RuleFixture.BlueprintPath },
        { 2, RuleFixture.BlueprintPath },
        { 3, RuleFixture.BlueprintPath },
        { 4, "Chronicle/2026/07/10-old.md" },
        { 5, RuleFixture.BlueprintPath },
        { 6, "tools/README.md" },
        { 8, RuleFixture.BlueprintPath },
        { 10, RuleFixture.BlueprintPath },
        { 11, "Chronicle/2026/07/10-old.md" },
        { 12, RuleFixture.BlueprintPath },
        { 15, null },
        { 16, "Chronicle/2026/07/10-old.md" },
        { 17, "Chronicle/2026/07/10-old.md" },
        { 18, "Chronicle/2026/07/10-old.md" },
        { 19, RuleFixture.BlueprintPath },
        { 20, RuleFixture.BlueprintPath },
        { 21, RuleFixture.BlueprintPath },
        { 22, RuleFixture.BlueprintPath },
        { 23, "Chronicle/2026/07/10-old.md" },
        { 25, "Chronicle/2026/07/10-old.md" },
        { 26, "Chronicle/2026/07/10-old.md" },
    };

    [Fact]
    public void DefaultFixtureUsesTheCanonicalDirectoryDigestionLedger()
    {
        var fixture = new RuleFixture();

        Assert.DoesNotContain(BackfillInventoryLoader.RelativePath, fixture.Files.Keys);
        var document = BackfillInventoryLoader.Load(fixture.Build().Current);
        var source = Assert.Single(document.RequireDigestionSources());
        var entry = Assert.Single(source.Entries);

        Assert.Equal("fixture-source", source.SourceId);
        Assert.Equal(RuleFixture.FixtureDigestionSourcePath, source.SourcePath);
        Assert.Equal(AtomizerRegistry.NoAtomizerId, source.Atomizer);
        Assert.Equal(RuleFixture.FixtureAtomId, entry.AtomId);
        Assert.Equal(RuleFixture.FixtureCasReference, entry.Fingerprints.RawSha256);
        Assert.Equal(RuleFixture.FixtureCasReference, entry.CasRef);
        Assert.Equal(DigestionMigrationState.Partial, entry.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
    }

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
        var changedPath = RuleFixture.ChangedPathForMutation(mutation);
        red.Changes.Clear();
        red.Changes.Add(changedPath);
        var redContext = number switch
        {
            20 => red.BuildForRuleCompatibility(),
            _ => red.Build(RawChangeSet.Create([changedPath])),
        };
        var redResult = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(number), redContext);

        Assert.NotEmpty(redResult.Diagnostics);
        Assert.All(
            redResult.Diagnostics,
            diagnostic => Assert.Equal(RuleId.CreateKnown(number), diagnostic.RuleId));
        Assert.Null(redResult.DeferredCase);
    }

    [Theory]
    [MemberData(nameof(BlockingCases))]
    public void CandidateThatChangesBlockingRuleInputStillWakesAndRejects(
        int number,
        string mutation)
    {
        var fixture = new RuleFixture();
        if (number == 16)
        {
            fixture.AddBackfillTargets();
        }
        fixture.Apply(mutation);
        var changedPath = RuleFixture.ChangedPathForMutation(mutation);
        fixture.Changes.Clear();
        fixture.Changes.Add(changedPath);
        var context = number == 20
            ? fixture.BuildForRuleCompatibility()
            : fixture.Build(RawChangeSet.Create([changedPath]));

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context)).Capability;

        Assert.Contains(RuleId.CreateKnown(number), completed.ExecutedRules);
        Assert.Contains(completed.Diagnostics, diagnostic => diagnostic.RuleId == RuleId.CreateKnown(number));
    }

    [Fact]
    public void Sl017ExecutesWhenAReferencedQueryTargetIsDeleted()
    {
        const string targetPath = "Library/notes/fixture-target.md";
        const string queries = """
            schema_version: 1
            queries:
              - id: D5-Q0099
                target_gid: D5/L/fixture-target
                doi: 10.1000/fixture
            """;
        var fixture = new RuleFixture();
        fixture.Files["Library/queries.yaml"] = queries;
        fixture.Baseline["Library/queries.yaml"] = queries;
        fixture.ForkPoint["Library/queries.yaml"] = queries;
        fixture.Baseline[targetPath] = "# Fixture target\n";
        fixture.ForkPoint[targetPath] = "# Fixture target\n";

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([targetPath])))).Capability;

        Assert.Contains(RuleId.CreateKnown(17), completed.ExecutedRules);
        Assert.Contains(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(17)
            && diagnostic.Path == "Library/queries.yaml"
            && diagnostic.Message.Contains("target GID is missing", StringComparison.Ordinal));
    }

    [Theory]
    [MemberData(nameof(AffectedInputs))]
    public void ActiveRuleExecutesWhenItsInputClosureChanges(int number, string path)
    {
        var fixture = new RuleFixture();
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([path])))).Capability;

        Assert.Contains(RuleId.CreateKnown(number), completed.ExecutedRules);
    }

    [Theory]
    [MemberData(nameof(UnaffectedInputs))]
    public void ActiveRuleIsRecordedAsSkippedWhenItsInputClosureDoesNotChange(
        int number,
        string? path)
    {
        var fixture = new RuleFixture();
        var changes = RawChangeSet.Create(path is null ? [] : [path]);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(changes))).Capability;
        var skippedProperty = typeof(CompletedRuleSet).GetProperty("SkippedRules");
        Assert.NotNull(skippedProperty);
        var skipped = Assert.IsType<ImmutableArray<RuleId>>(skippedProperty!.GetValue(completed));

        Assert.DoesNotContain(RuleId.CreateKnown(number), completed.ExecutedRules);
        Assert.Contains(RuleId.CreateKnown(number), skipped);
    }

    [Fact]
    public void MetaSplitScriptIsAnUnknownArtifactRatherThanAnInstantiationTicket()
    {
        Assert.True(RuleId.TryCreate("SL-000", out var sl000));
        const string path = "Meta/split.py";
        var fixture = new RuleFixture();
        fixture.Files[path] = "print('split')\n";

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(
                fixture.Build(RawChangeSet.Create([path]))));

        Assert.DoesNotContain(
            completed.Capability.Diagnostics,
            diagnostic => diagnostic.Path == path
                && diagnostic.RuleId == RuleId.CreateKnown(21)
                && diagnostic.Message == "Meta/split.py 未实例化(案号 D5-T0004)");
        var diagnostic = Assert.Single(
            completed.Capability.Diagnostics,
            diagnostic => diagnostic.Path == path && diagnostic.RuleId == sl000);
        Assert.Equal("unknown Meta artifact", diagnostic.Message);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Fact]
    public void Sl019AcceptsAFreeProseTaskAsAnAnomalyCaseAddress()
    {
        const string path = "D5/X_Frontier/FreeProseTask.lean";
        var fixture = new RuleFixture();
        fixture.AddTask(path, "D5/X_Frontier/FreeProseTask", "D5-T0097");
        fixture.Files["Evidence/D5/S0/Carrier/Result.run.json"] =
            "{\"anomaly\":\"fixture drift\",\"case_id\":\"D5-T0097\"}\n";

        var diagnostics = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(19), fixture.Build()).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Theory]
    [InlineData("outer-comment")]
    [InlineData("five-digit")]
    public void RepositoryRulesTaskTokenRecognitionRetainsDevSemantics(string scenario)
    {
        const string path = "D5/X_Frontier/DevTaskTokenSemantics.lean";
        const string gid = "D5/X_Frontier/DevTaskTokenSemantics";
        const string caseId = "D5-T0097";
        var fixture = new RuleFixture();
        fixture.AddTask(path, gid, scenario == "five-digit" ? caseId + "0" : caseId);
        if (scenario == "outer-comment")
        {
            fixture.Files[path] = fixture.Files[path].Replace(
                "/-- TASK D5-T0097",
                "/-\n/-- TASK D5-T0097",
                StringComparison.Ordinal) + "-/\n";
        }

        fixture.Files["Evidence/D5/S0/Carrier/Result.run.json"] =
            $"{{\"anomaly\":\"fixture drift\",\"case_id\":\"{caseId}\"}}\n";

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build()).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Fact]
    public void DirectoryBackfillReachesSharedDownstreamValidationWithoutFormatDiagnostics()
    {
        var fixture = new RuleFixture();
        fixture.UseSyntheticDirectoryBackfill();

        var diagnostics = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build()).Diagnostics;

        Assert.DoesNotContain(diagnostics, diagnostic =>
            diagnostic.Message.Contains("canonical", StringComparison.Ordinal)
            || diagnostic.Message.Contains("metadata", StringComparison.Ordinal)
            || diagnostic.Message.Contains("ticket index", StringComparison.Ordinal)
            || diagnostic.Message.Contains("directory", StringComparison.Ordinal));
        Assert.Contains(diagnostics, diagnostic =>
            diagnostic.Message.Contains("fingerprint", StringComparison.Ordinal)
            || diagnostic.Message.Contains("CAS", StringComparison.Ordinal));
    }

    [Fact]
    public void ValidDirectoryBackfillIsGreenWithDirectoryBaseline()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.UseValidDirectoryBackfill();

        var diagnostics = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build()).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Fact]
    public void Sl016DifferentialIgnoresUnavailableBaselineGenreProjection()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.ForkPoint[RuleFixture.FixtureBackfillSourcePath] = RemoveGenreMarkers(
            fixture.ForkPoint[RuleFixture.FixtureBackfillSourcePath]);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build()).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Fact]
    public void Sl016RejectsLegacyGenreMarkerSchemaInCandidate()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureBackfillSourcePath] = RemoveGenreMarkers(
            fixture.Files[RuleFixture.FixtureBackfillSourcePath]);

        var diagnostic = Assert.Single(RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build()).Diagnostics);

        Assert.Equal(
            $"source metadata keys are not canonical: {RuleFixture.FixtureBackfillSourcePath}",
            diagnostic.Message);
    }

    [Fact]
    public void Sl016ChecksMissingCasBlobBeforeOtherReceiptValidationCanReturnEarly()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] = fixture.Files[
                RuleFixture.FixtureBackfillAtomPath]
            .Replace(
                "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget",
                "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget\n  - D5/S0/Carrier/BackfillTarget",
                StringComparison.Ordinal);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build()).Diagnostics;

        Assert.Contains(diagnostics, diagnostic => diagnostic.Message ==
            $"entry {RuleFixture.FixtureAtomId} CAS blob is missing: {RuleFixture.FixtureCasPath}");
    }

    private static string RemoveGenreMarkers(string metadata) => metadata
        .Replace("genre_registry_check = \"no-registry\"\n", string.Empty, StringComparison.Ordinal)
        .Replace("unregistered_genres = []\n", string.Empty, StringComparison.Ordinal);

    [Fact]
    public void Sl016ChecksCasBlobHashBeforeOtherReceiptValidationCanReturnEarly()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Changes.Clear();
        fixture.Changes.Add(RuleFixture.FixtureCasPath);
        fixture.Files[RuleFixture.FixtureCasPath] = "corrupt";
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] = fixture.Files[
                RuleFixture.FixtureBackfillAtomPath]
            .Replace(
                "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget",
                "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget\n  - D5/S0/Carrier/BackfillTarget",
                StringComparison.Ordinal);

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build()));

        Assert.Contains(completed.Capability.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(16)
            && diagnostic.Message.Contains(
                $"entry {RuleFixture.FixtureAtomId} CAS blob hash mismatch: {RuleFixture.FixtureCasPath}",
                StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016DoesNotReplayCommittedCasIntegrityForAnUnrelatedCandidateDelta()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureCasPath] = "trusted committed bytes";
        var context = fixture.Build(RawChangeSet.Create(["notes/unrelated.txt"]));

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context));

        Assert.DoesNotContain(
            completed.Capability.Diagnostics,
            static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(16));
    }

    [Fact]
    public void Sl016RechecksCoverageReceiptWhenFrozenStatementChanges()
    {
        var (fixture, frozenChanges) = FrozenStatementDriftFixture();
        var changes = RawChangeSet.Create(frozenChanges);
        var context = fixture.Build(changes);
        var document = BackfillInventoryLoader.Load(context.Current);
        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            context.Current,
            context.Lean,
            baselineDocument: BackfillInventoryLoader.Load(context.ForkPoint),
            baselineSnapshot: context.ForkPoint,
            casEvaluation: DigestionCasStore.Evaluate(document, context.Current, changes),
            changes: changes);

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
        Assert.Contains(
            Assert.Single(evaluation.Entries).Gaps,
            static gap => gap.Code == "coverage-receipt-mismatch");
    }

    [Fact]
    public void LeanToolchainChangeWakesSl016BecauseItsLeanReportInputCanDrift()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create(["lean-toolchain"]));

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
    }

    [Theory]
    [InlineData("tools/StrataLint.Engine/Digestion/Atomizers/PzgAtomizer.cs")]
    [InlineData("tools/StrataLint.Engine/StrataLint.Engine.csproj")]
    [InlineData("Directory.Build.props")]
    [InlineData("Directory.Build.targets")]
    [InlineData("Directory.Packages.props")]
    [InlineData("global.json")]
    public void EveryAtomizerBuildInputWakesSl016BecauseItsProjectionCanDrift(string changedPath)
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([changedPath]));

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
    }

    [Fact]
    public void Sl016DerivedStatusIsTheSameWhetherOrNotFrozenStatementDriftIsInTheCandidateDelta()
    {
        // Skipping historical receipt replay must reuse the base verdict rather than turn a
        // partial entry into absorbed. The stale receipt itself is reported only when its
        // authority input is in the candidate delta.
        const string coverageGid = "D5/S0/Carrier/BackfillTarget";
        var (fixture, frozenChanges) = FrozenStatementDriftFixture();

        var touched = StatementDriftEvaluation(
            fixture,
            RawChangeSet.Create(frozenChanges));
        var untouched = StatementDriftEvaluation(
            fixture,
            RawChangeSet.Create(["notes/unrelated.txt"]));

        Assert.Contains(touched.Gaps, gap =>
            gap.Code == "coverage-receipt-mismatch" && gap.Detail == coverageGid);
        Assert.DoesNotContain(untouched.Gaps, static gap => gap.Code == "coverage-receipt-mismatch");
        Assert.Equal(DigestionMigrationState.Partial, untouched.DerivedStatus.Migration);
        Assert.Equal(touched.DerivedStatus, untouched.DerivedStatus);
    }

    [Fact]
    public void Sl016ComparesProjectedStatusOnlyWhenItsAuthorityClosureChanges()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            var atom = files[RuleFixture.FixtureBackfillAtomPath];
            files.Remove(RuleFixture.FixtureBackfillAtomPath);
            files[$"{BackfillInventoryLoader.RootPath}fixture-source/absorbed-closed/fixture-atom.yaml"] = atom;
        }

        var unrelated = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(
            fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintPath])))).Capability;

        Assert.DoesNotContain(unrelated.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("handwritten status", StringComparison.Ordinal));

        fixture.Files[RuleFixture.FixtureDigestionSourcePath] += "changed";
        var relevant = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(
            fixture.Build(RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath])))).Capability;

        Assert.Contains(relevant.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("handwritten status", StringComparison.Ordinal));
    }

    private static DigestionEntryEvaluation StatementDriftEvaluation(
        RuleFixture fixture,
        RawChangeSet changes)
    {
        var context = fixture.Build(changes);
        var document = BackfillInventoryLoader.Load(context.Current);
        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            context.Current,
            context.Lean,
            baselineDocument: BackfillInventoryLoader.Load(context.ForkPoint),
            baselineSnapshot: context.ForkPoint,
            casEvaluation: DigestionCasStore.Evaluate(document, context.Current, changes),
            changes: changes);
        return Assert.Single(evaluation.Entries);
    }

    private static (RuleFixture Fixture, string[] FrozenChanges) FrozenStatementDriftFixture()
    {
        const string coverageGid = "D5/S0/Carrier/BackfillTarget";
        const string targetPath = coverageGid + ".lean";
        var baselineStatementId = FrozenStatementReceiptTestData.Id('a');
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[targetPath] = fixture.Files[targetPath];
            files[RuleFixture.FixtureBackfillAtomPath] = files[RuleFixture.FixtureBackfillAtomPath]
                .Replace(
                    "coverage: []",
                    "coverage:\n"
                    + $"    - gid: {coverageGid}\n"
                    + $"      source_sha256: {RuleFixture.FixtureCasReference}\n"
                    + $"      target_statement_id: {baselineStatementId}",
                    StringComparison.Ordinal);
        }

        InstallFrozenStatement(fixture.Files, targetPath, FrozenStatementReceiptTestData.Id('b'));
        InstallFrozenStatement(fixture.Baseline, targetPath, baselineStatementId);
        InstallFrozenStatement(fixture.ForkPoint, targetPath, baselineStatementId);
        var currentEvents = fixture.Files.Keys
            .Where(static path => FrozenLedgerChangeClassifier.IsAcceptedEventPath(path));
        var baselineEvents = fixture.Baseline.Keys
            .Where(static path => FrozenLedgerChangeClassifier.IsAcceptedEventPath(path));
        var frozenChanges = currentEvents
            .Except(baselineEvents, StringComparer.Ordinal)
            .Concat(baselineEvents.Except(currentEvents, StringComparer.Ordinal))
            .ToArray();
        Assert.NotEmpty(frozenChanges);
        return (fixture, frozenChanges);
    }

    private static void InstallFrozenStatement(
        IDictionary<string, string> files,
        string targetPath,
        string statementId) =>
        FrozenStatementReceiptTestData.AddLedger(
            files,
            new FrozenStatementReceiptTestData.Module(targetPath, statementId, []));

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
            RuleCatalog.Default.EvaluateSingle(
                RuleId.CreateKnown(1),
                forbidden.Build(RawChangeSet.Create([RuleFixture.AssumptionDebtPath]))).Diagnostics);
        Assert.Equal(RuleId.CreateKnown(1), diagnostic.RuleId);
        Assert.Equal(RuleFixture.AssumptionDebtPath, diagnostic.Path);
        Assert.Contains("may not import", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl018RejectsValuesOutsideTheCanonicalProjectionAddress()
    {
        var fixture = new RuleFixture();
        fixture.Files["Evidence/D5/values.result.json"] =
            "{\"D5/sample\": {\"status\": \"verified\", \"value\": 123}}\n";

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(
                RuleId.CreateKnown(18),
                fixture.Build(RawChangeSet.Create(["Evidence/D5/values.result.json"]))).Diagnostics);

        Assert.Equal("canonical values projection must be Evidence/D5/values.json", diagnostic.Message);
    }

    [Fact]
    public void Sl018AcceptsTheCanonicalProjectionWithoutReverifyingItsBytes()
    {
        var fixture = new RuleFixture();
        fixture.AddValuesProjection();
        fixture.Files[RuleFixture.ValuesProjectionPath] += "\n";

        Assert.Empty(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(18), fixture.Build()).Diagnostics);
    }

    [Fact]
    public void Sl025DoesNotGovernBlueprintMarkdownContent()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.BlueprintPath] = "# Arbitrary reader snapshot\n";

        Assert.Empty(EvaluateSl025(fixture));
        Assert.Equal(
            "Blueprint source-projection skeleton",
            RuleCatalog.Default.Descriptors.Single(
                descriptor => descriptor.Id == RuleId.CreateKnown(25)).Title);
    }

    [Fact]
    public void Sl025RejectsBlueprintMarkdownWithoutMatchingScribeSource()
    {
        var fixture = new RuleFixture();
        fixture.Files.Remove(RuleFixture.BlueprintSourcePath);

        var diagnostic = Assert.Single(EvaluateSl025(fixture), item =>
            item.Path == RuleFixture.BlueprintPath);

        Assert.Equal("Blueprint markdown has no matching .scribe.cs source", diagnostic.Message);
    }

    [Fact]
    public void Sl025RejectsScribeSourceWithoutMatchingMarkdownProjection()
    {
        var fixture = new RuleFixture();
        fixture.Files.Remove(RuleFixture.BlueprintPath);

        var diagnostic = Assert.Single(EvaluateSl025(fixture), item =>
            item.Path == RuleFixture.BlueprintSourcePath);

        Assert.Equal("Blueprint Scribe source has no matching .md projection", diagnostic.Message);
    }

    private static ImmutableArray<Diagnostic> EvaluateSl025(RuleFixture fixture)
    {
        Assert.True(RuleId.TryCreate("SL-025", out var ruleId));
        var context = fixture.Changes.Any(path =>
                path.EndsWith(".scribe.cs", StringComparison.Ordinal))
            ? fixture.BuildForProtectedRuleCompatibility()
            : fixture.Build();
        return RuleCatalog.Default.EvaluateSingle(ruleId!, context).Diagnostics;
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
            .Concat(new[] { 7, 9, 13, 14, 22, 23 })
            .Order()
            .ToArray();

        Assert.Equal(Enumerable.Range(1, 23).Append(25).Append(26), exercised);
    }

    [Fact]
    public void Sl019AcceptsAValidTowerManifestAsAKnownGovernanceSchema()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.TowerManifestPath] = """
            schema_version: 1
            components:
              - id: failure-detector
                kind: repository-files
                members:
                  - tools/TOWER.yaml
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
        fixture.Files[RuleFixture.TowerManifestPath] = """
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
            fixture.Build(RawChangeSet.Create([RuleFixture.TowerManifestPath])));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Contains(
            "invalid TOWER schema: tower components[0] keys are not canonical",
            diagnostic.Message,
            StringComparison.Ordinal);
    }
}
