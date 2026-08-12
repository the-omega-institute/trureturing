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
    public void DirectoryBackfillRejectsDanglingTicketGid()
    {
        var fixture = new RuleFixture();
        fixture.UseSyntheticDirectoryBackfill("D5-T0098 = \"D5/X_Frontier/SyntheticDelta\"\n");

        var diagnostics = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build()).Diagnostics;

        Assert.Contains(diagnostics, diagnostic =>
            diagnostic.Message == "dangling ticket D5-T0098: ticket target Lean file is absent");
    }

    [Fact]
    public void DirectoryBackfillRejectsDuplicateTicketCaseId()
    {
        var fixture = new RuleFixture();
        fixture.UseSyntheticDirectoryBackfill(
            $"D5-T0098 = \"{RuleFixture.RingPath[..^".lean".Length]}\"\n"
            + $"D5-T0098 = \"{RuleFixture.RingPath[..^".lean".Length]}\"\n");

        var diagnostics = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build()).Diagnostics;

        Assert.Contains(diagnostics, diagnostic => diagnostic.Message == "duplicate ticket case: D5-T0098");
    }

    [Fact]
    public void DirectoryBackfillRejectsUnregisteredFrontierTask()
    {
        var fixture = new RuleFixture();
        fixture.UseSyntheticDirectoryBackfill("");
        fixture.AddSyntheticUnregisteredFrontierTask("D5-T0097");

        var diagnostics = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build()).Diagnostics;

        Assert.Contains(diagnostics, diagnostic =>
            diagnostic.Message == "frontier TASK cases are missing from ticket_index: D5-T0097");
    }

    [Fact]
    public void DirectoryBackfillReachesSharedDownstreamValidationWithoutFormatDiagnostics()
    {
        var fixture = new RuleFixture();
        fixture.UseSyntheticDirectoryBackfill("");

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
        Assert.Contains(
            $"soft limit {RepositoryRules.ArtifactSoftLineLimit}",
            softDiag.Message,
            StringComparison.Ordinal);

        // > 800: a hard block.
        var hard = new RuleFixture();
        hard.Files[RuleFixture.RingPath] += string.Concat(Enumerable.Repeat("-- pad\n", 801));
        var hardDiag = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), hard.Build()).Diagnostics);
        Assert.Equal(AdmissionEffect.Block, hardDiag.AdmissionEffect);
        Assert.Equal("artifact exceeds 800 lines", hardDiag.Message);
    }

    [Fact]
    public void Sl003DoesNotTreatTheSingleSourceDigestionLedgerAsASplittableModule()
    {
        var fixture = new RuleFixture();

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;

        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Path == "Meta/BACKFILL.yaml");
    }

    [Fact]
    public void Sl003DoesNotTreatTheCasObjectStoreAsASplittableModule()
    {
        var fixture = new RuleFixture();
        for (var index = 0; index < 13; index++)
        {
            var text = $"CAS object {index}\n";
            var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes(text));
            fixture.Files[captured.RelativePath] = text;
            // The change has to touch the store, or the capacity rule skips it for being
            // untouched and this stops testing the exclusion it is named for.
            fixture.Changes.Add(captured.RelativePath);
        }

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;

        Assert.DoesNotContain(diagnostics, diagnostic =>
            diagnostic.Path.StartsWith(DigestionCasStore.RootPath, StringComparison.Ordinal)
            || diagnostic.Path == DigestionCasStore.RootPath.TrimEnd('/'));
    }

    [Fact]
    public void Sl003RefusesAnOverfullBucketTheChangeTouches()
    {
        var fixture = OverfullBucket();
        fixture.Changes.Add($"{OverfullBucketPath}/Member00.lean");

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics,
            item => item.Path == OverfullBucketPath);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        // Read from the constants, not from a literal. The old message said "maximum 12" flat,
        // with the 12 typed into the string rather than interpolated, so it named the admission
        // capacity as if it were the only limit and would have kept saying 12 after a change to
        // DirectoryFileLimit. The repository-wide net tolerates DirectoryToleranceLimit above it;
        // an overfull bucket is split pressure, not a correctness fault.
        Assert.Equal(
            $"directory contains 13 files (admission capacity {RepositoryRules.DirectoryFileLimit}; "
            + $"the repository-wide net tolerates {RepositoryRules.DirectoryToleranceLimit} — "
            + "split per CLAUDE.md 8)",
            diagnostic.Message);
    }

    [Fact]
    public void Sl003LeavesAnOverfullBucketAloneWhenTheChangeDoesNotTouchIt()
    {
        var fixture = OverfullBucket();

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;

        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Path == OverfullBucketPath);
    }

    private const string OverfullBucketPath = "D5/S0/Overfull";

    private static RuleFixture OverfullBucket()
    {
        var fixture = new RuleFixture();
        for (var index = 0; index < 13; index++)
        {
            var path = $"{OverfullBucketPath}/Member{index:00}.lean";
            fixture.Files[path] = "-- member\n";
            fixture.Reports[path] = new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray<LeanDeclaration>.Empty);
        }

        return fixture;
    }

    [Fact]
    public void Sl013RejectsCodexFailedAttributionWithoutReference()
    {
        var fixture = new RuleFixture();
        fixture.AddTask(
            "D5/X_Frontier/CodexFailure.lean",
            "D5/X_Frontier/CodexFailure",
            "D5-T0090",
            "[codex-failed] candidate returned no result");

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(13), fixture.Build()).Diagnostics);

        Assert.Equal(
            "codex-failed autopsy for D5-T0090 requires a valid [codex-log:<rooted-path>] reference",
            diagnostic.Message);
    }

    [Fact]
    public void Sl013RejectsCodexFailedAttributionWithMalformedReference()
    {
        var fixture = new RuleFixture();
        fixture.AddTask(
            "D5/X_Frontier/CodexFailure.lean",
            "D5/X_Frontier/CodexFailure",
            "D5-T0091",
            "[codex-failed] [codex-log:logs/latest.txt]");

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(13), fixture.Build()).Diagnostics);

        Assert.Equal(
            "codex-failed autopsy for D5-T0091 requires a valid [codex-log:<rooted-path>] reference",
            diagnostic.Message);
    }

    [Theory]
    [InlineData("~/.codex/sessions/2026/08/09/rollout-fixture.jsonl")]
    [InlineData("<RT>/logs/codex-adoption/fixture/result.json")]
    [InlineData("~/Library/Logs/fkst/codex/worktree-fixture.log")]
    public void Sl013AcceptsCodexFailedAttributionWithValidReference(string logPath)
    {
        var fixture = new RuleFixture();
        fixture.AddTask(
            "D5/X_Frontier/CodexFailure.lean",
            "D5/X_Frontier/CodexFailure",
            "D5-T0092",
            $"[codex-failed] [codex-log:{logPath}]");

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(13),
            fixture.Build()).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Fact]
    public void Sl013StillRejectsShortenedAutopsy()
    {
        const string path = "D5/X_Frontier/AutopsyHistory.lean";
        var fixture = new RuleFixture();
        fixture.AddTask(path, "D5/X_Frontier/AutopsyHistory", "D5-T0093", "first attempt");
        fixture.Baseline[path] = fixture.Files[path].Replace(
            "尸检:first attempt",
            "尸检:first attempt; second attempt",
            StringComparison.Ordinal);
        fixture.BaselineReports[path] = fixture.Reports[path];

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(13), fixture.Build()).Diagnostics);

        Assert.Equal("autopsy for D5-T0093 was shortened", diagnostic.Message);
    }

    [Fact]
    public void Sl013DoesNotTreatUnstructuredCodexFailedTextAsAttribution()
    {
        var fixture = new RuleFixture();
        fixture.AddTask(
            "D5/X_Frontier/OrdinaryAutopsy.lean",
            "D5/X_Frontier/OrdinaryAutopsy",
            "D5-T0094",
            "ordinary text mentions codex-failed without the attribution marker");

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(13),
            fixture.Build()).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Fact]
    public void Sl018RejectsValuesOutsideTheCanonicalProjectionAddress()
    {
        var fixture = new RuleFixture();
        fixture.Files["Evidence/D5/values.result.json"] =
            "{\"D5/sample\": {\"status\": \"verified\", \"value\": 123}}\n";

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(18), fixture.Build()).Diagnostics);

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
    public void Sl025RejectsChangedBlueprintMarkdownWithoutChangedScribeSource()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.BlueprintPath] = "# Changed golden ring\n";

        var diagnostic = Assert.Single(EvaluateSl025(fixture));

        Assert.Equal(RuleFixture.BlueprintPath, diagnostic.Path);
        Assert.Equal(
            "Blueprint markdown is a projection: emit it from a .scribe.cs change",
            diagnostic.Message);
    }

    [Fact]
    public void Sl025AcceptsChangedBlueprintMarkdownWithChangedScribeSource()
    {
        const string sourcePath = "Blueprint/D5/S0/Carrier/Ring.scribe.cs";
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.BlueprintPath] = "# Changed golden ring\n";
        fixture.Files[sourcePath] = "// changed source\n";
        fixture.Baseline[sourcePath] = "// baseline source\n";
        fixture.Changes.Add(sourcePath);

        Assert.Empty(EvaluateSl025(fixture));
    }

    [Fact]
    public void Sl025AcceptsUnchangedBlueprintMarkdownListedInChanges()
    {
        var fixture = new RuleFixture();

        Assert.Empty(EvaluateSl025(fixture));
    }

    [Fact]
    public void Sl025AcceptsChangedScribeSourceWithoutBlueprintMarkdown()
    {
        const string sourcePath = "Blueprint/D5/S0/Carrier/Ring.scribe.cs";
        var fixture = new RuleFixture();
        fixture.Changes.Clear();
        fixture.Changes.Add(sourcePath);
        fixture.Files[sourcePath] = "// changed source\n";
        fixture.Baseline[sourcePath] = "// baseline source\n";

        Assert.Empty(EvaluateSl025(fixture));
    }

    private static ImmutableArray<Diagnostic> EvaluateSl025(RuleFixture fixture)
    {
        Assert.True(RuleId.TryCreate("SL-025", out var ruleId));
        var context = fixture.Changes.Any(path => path.EndsWith(".scribe.cs", StringComparison.Ordinal))
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
            .Concat(new[] { 7, 9, 14, 22, 23, 25 })
            .Order()
            .ToArray();

        Assert.Equal(Enumerable.Range(1, 23).Append(25), exercised);
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
            fixture.Build());

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Contains(
            "invalid TOWER schema: tower components[0] keys are not canonical",
            diagnostic.Message,
            StringComparison.Ordinal);
    }
}
