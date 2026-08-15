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
    public void MetaSplitScriptIsAnUnknownArtifactRatherThanAnInstantiationTicket()
    {
        Assert.True(RuleId.TryCreate("SL-000", out var sl000));
        const string path = "Meta/split.py";
        var fixture = new RuleFixture();
        fixture.Files[path] = "print('split')\n";

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.BuildForRuleCompatibility()));

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
    public void Sl016ChecksMissingCasBlobBeforeOtherReceiptValidationCanReturnEarly()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Files[BackfillInventoryLoader.RelativePath] = fixture.Files[
                BackfillInventoryLoader.RelativePath]
            .Replace(
                "                coverage_gids:\n                  - D5/S0/Carrier/BackfillTarget",
                "                coverage_gids:\n                  - D5/S0/Carrier/BackfillTarget\n                  - D5/S0/Carrier/BackfillTarget",
                StringComparison.Ordinal);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build()).Diagnostics;

        Assert.Contains(diagnostics, diagnostic => diagnostic.Message ==
            $"entry {RuleFixture.FixtureAtomId} CAS blob is missing: {RuleFixture.FixtureCasPath}");
    }

    [Fact]
    public void Sl016ChecksCasBlobHashBeforeOtherReceiptValidationCanReturnEarly()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureCasPath] = "corrupt";
        fixture.Files[BackfillInventoryLoader.RelativePath] = fixture.Files[
                BackfillInventoryLoader.RelativePath]
            .Replace(
                "                coverage_gids:\n                  - D5/S0/Carrier/BackfillTarget",
                "                coverage_gids:\n                  - D5/S0/Carrier/BackfillTarget\n                  - D5/S0/Carrier/BackfillTarget",
                StringComparison.Ordinal);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build()).Diagnostics;

        Assert.Contains(diagnostics, diagnostic => diagnostic.Message.Contains(
            $"entry {RuleFixture.FixtureAtomId} CAS blob hash mismatch: {RuleFixture.FixtureCasPath}",
            StringComparison.Ordinal));
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
            "Blueprint markdown is a projection: emit it from a Scribe or digestion source change",
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
    public void Sl025AcceptsChangedBlueprintMarkdownWithChangedDigestionLedgerSource()
    {
        const string sourcePath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        fixture.Files[RuleFixture.BlueprintPath] = "# Changed golden ring\n";
        fixture.Files[sourcePath] = fixture.Files[sourcePath].Replace(
            "D5/S0/Carrier/BackfillTarget",
            "D5/S0/Carrier/Ring.goldenRing",
            StringComparison.Ordinal);
        fixture.Changes.Add(sourcePath);

        Assert.Empty(EvaluateSl025(fixture));
    }

    [Fact]
    public void Sl025RejectsChangedBlueprintMarkdownWithUnrelatedDigestionLedgerSource()
    {
        const string sourcePath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        fixture.Files[RuleFixture.BlueprintPath] = "# Changed golden ring\n";
        fixture.Files[sourcePath] += "\n";
        fixture.Changes.Add(sourcePath);

        var diagnostic = Assert.Single(EvaluateSl025(fixture));

        Assert.Equal(RuleFixture.BlueprintPath, diagnostic.Path);
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
    public void Sl025RejectsScribeSourceWithoutMatchingBlueprintMarkdown()
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
            .Concat(new[] { 7, 9, 13, 14, 22, 23, 25 })
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
            fixture.Build());

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Contains(
            "invalid TOWER schema: tower components[0] keys are not canonical",
            diagnostic.Message,
            StringComparison.Ordinal);
    }
}
