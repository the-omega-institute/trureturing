using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void DigestStatusValidatesCurrentCoverageEdge()
    {
        var environment = DigestStatusHistoricalCoverageEnvironment();

        var result = environment.DigestStatus(["--json"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-target-mismatch", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusReportsCasSeenAcrossNormalizedSourceRewrite()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var ledgerBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\r\n\r\n**定理 1.1(Test)**。claim。\r\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, ledgerBytes, DigestionTestSupport.Rules).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Files[captured.RelativePath] = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files[RuleFixture.FixtureBackfillSourcePath] =
            $"source_id = \"fixture-source\"\n"
            + $"path = \"{RuleFixture.FixtureDigestionSourcePath}\"\n"
            + $"atomizer = \"{atomizerId}\"\n"
            + "genre_registry_check = \"collected\"\n"
            + "unregistered_genres = []\n";
        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        fixture.Files[$"{BackfillInventoryLoader.RootPath}fixture-source/residual-open/{AtomId(atom)}.yaml"] = $$"""
            fingerprints:
              raw_sha256: {{atom.Fingerprints.RawSha256}}
              normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
            cas_ref: {{captured.Reference}}
            coverage_gids: []
            receipts:
              unresolved_subitems: []
              chain_atoms: []
              tail_authorization: null
            """;
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"alignment\": \"seen\"", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("normalized-seen-not-deletable", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"deletable\": false", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusReadsTheDirectoryFormDigestionLedger()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"entries_total\": 1", result.Output, StringComparison.Ordinal);
        Assert.Contains($"\"atom_id\": \"{RuleFixture.FixtureAtomId}\"", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusReportsEveryEntryAndZeroCurrentlyDeletable()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"entries_total\": 1", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"deletable_now\": 0", result.Output, StringComparison.Ordinal);
        Assert.Contains($"\"atom_id\": \"{RuleFixture.FixtureAtomId}\"", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusJsonAndTextEntriesExposeCoverageGidsDerivedFromCoverageEdges()
    {
        var fingerprints = new DigestionFingerprints(
            "sha256:" + new string('a', 64),
            "sha256:" + new string('b', 64));
        var status = new DigestionStatus(
            DigestionMigrationState.Partial,
            DigestionTruthState.Open);
        var entry = new DigestionLedgerEntry(
            "source",
            "synthetic/source.md",
            AtomizerRegistry.NoAtomizerId,
            "atom",
            fingerprints,
            [
                new DigestionCoverageEdge("D5/S0/Carrier/Zeta", null),
                new DigestionCoverageEdge("D5/S0/Carrier/Alpha", null),
            ],
            new DigestionReceipts([], [], null),
            status,
            fingerprints.RawSha256);
        var evaluation = new DigestionLedgerEvaluation(
            [new DigestionEntryEvaluation(
                entry,
                DigestionReceiptAlignment.Seen,
                status,
                false,
                [])],
            []);

        var json = DigestStatusCommand.RenderJson(
            evaluation,
            DigestionFrontierTestProjection.Create(evaluation));
        var text = DigestStatusCommand.RenderText(evaluation);

        using var document = JsonDocument.Parse(json);
        var jsonEntry = Assert.Single(document.RootElement.GetProperty("entries").EnumerateArray());
        Assert.Equal(
            ["D5/S0/Carrier/Alpha", "D5/S0/Carrier/Zeta"],
            jsonEntry.GetProperty("coverage_gids")
                .EnumerateArray()
                .Select(static item => item.GetString()));
        Assert.Contains(
            "coverage_gids=[D5/S0/Carrier/Alpha,D5/S0/Carrier/Zeta]",
            text,
            StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusResidualSummaryUsesMachineDerivedUnresolvedSubitemGaps()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] = fixture.Files[
                RuleFixture.FixtureBackfillAtomPath]
            .Replace(
                "  unresolved_subitems: []",
                "  unresolved_subitems:\n    - zeta-residual\n    - alpha-residual",
                StringComparison.Ordinal);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--residual-summary"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("- unresolved_subitems: 2", result.Output, StringComparison.Ordinal);
        Assert.Contains("- mother_residual_atom_ids: 1", result.Output, StringComparison.Ordinal);
        Assert.Contains($"- `{RuleFixture.FixtureAtomId}` (2)", result.Output, StringComparison.Ordinal);
        Assert.True(
            result.Output.IndexOf("`alpha-residual`", StringComparison.Ordinal)
                < result.Output.IndexOf("`zeta-residual`", StringComparison.Ordinal));
    }

    [Fact]
    public void DigestStatusReportsHistoricalAndCurrentContentAsSeen()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var currentAtom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            currentBytes,
            DigestionTestSupport.Rules).Claims);
        var baselineLedger = IngestLedger(atomizerId, oldAtom);
        var baselineDocument = baselineLedger;
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var planningSnapshot = Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [TheoryAtomizerDataLoader.DataPath] = Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes),
            [RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes),
            [oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan()),
        }));
        var plan = ReportFreeDigestionIngestor.Plan(baselineDocument, planningSnapshot);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, plan.Document);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, baselineLedger);
        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Baseline.Remove(RuleFixture.FixtureCasPath);
        fixture.Files[oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan());
        fixture.Baseline[oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan());
        foreach (var item in plan.CasObjects)
        {
            fixture.Files[item.RelativePath] = Encoding.UTF8.GetString(item.Bytes.AsSpan());
        }

        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var entries = json.RootElement.GetProperty("entries").EnumerateArray().ToArray();
        var historical = Assert.Single(
            entries,
            entry => entry.GetProperty("atom_id").GetString() == AtomId(oldAtom));
        var current = Assert.Single(
            entries,
            entry => entry.GetProperty("atom_id").GetString() == AtomId(currentAtom));
        Assert.Equal("seen", historical.GetProperty("alignment").GetString());
        Assert.Equal("seen", current.GetProperty("alignment").GetString());
    }

    [Fact]
    public void DigestStatusValidatesGenreProjection()
    {
        var fixture = CandidateFixtureWithInvalidGenreProjection();
        var environment = DigestStatusEnvironment(fixture);

        var result = environment.DigestStatus(["--json"]);

        Assert.False(result.Success);
        Assert.Contains("invalid genre_registry_check", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ResidualShardsAreRenderedPerSource()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create(Array.Empty<string>()),
            Snapshot(fixture.Files),
            null);

        var (_, shards) = DigestStatusCommand.RenderResidual(
            repository,
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)));

        Assert.Contains("Generated/echo-residuals/fixture-source.md", shards.Keys);
    }

    [Fact]
    public void DigestStatusReportsTheDerivedStatusWhenTheRecordedOneDiffers()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var expected = RunDigestStatus(fixture);
        var atom = fixture.Files[RuleFixture.FixtureBackfillAtomPath];
        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        var statusPath = $"{BackfillInventoryLoader.RootPath}fixture-source/absorbed-closed/{RuleFixture.FixtureAtomId}.yaml";
        fixture.Files[statusPath] = atom;

        var result = RunDigestStatus(fixture);

        Assert.True(expected.Success, expected.Error);
        Assert.True(result.Success, result.Error);
        Assert.Equal(expected.Output, result.Output);
    }

    private static ProductionCliEnvironment DigestStatusEnvironment(RuleFixture fixture) => new(
        "/repo",
        new FakeRepositoryGateway(
            RawChangeSet.Create(Array.Empty<string>()),
            Snapshot(fixture.Files),
            null),
        new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
        new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

    private static ProductionCliEnvironment DigestStatusHistoricalCoverageEnvironment()
    {
        const string gid = "D5/S0/Carrier/BackfillTarget";
        var absorbedPath =
            $"Meta/Digestion/backfill/fixture-source/absorbed-closed/{RuleFixture.FixtureAtomId}.yaml";
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var definitionPath = ScribeEmissionAttestation.DefinitionPath(gid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(gid);
        const string definition = "fixture definition\n";
        const string emission = "# Fixture emission\n";
        var definitionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(definition)).RawSha256;
        var emissionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(emission)).RawSha256;
        var atom = fixture.Files[RuleFixture.FixtureBackfillAtomPath]
            .Replace(
                "target_statement_id: null",
                "target_statement_id: sha256:0000000000000000000000000000000000000000000000000000000000000000",
                StringComparison.Ordinal);

        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        fixture.Files[absorbedPath] = atom;
        fixture.Files[definitionPath] = definition;
        fixture.Files[emissionPath] = emission;

        var verified = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                gid,
                definitionPath,
                definitionSha256,
                emissionPath,
                emissionSha256),
        ]);
        return new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(verified));
    }

    private static CommandResult RunDigestStatus(RuleFixture fixture) =>
        new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), Snapshot(fixture.Files), null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty))
        .DigestStatus(Array.Empty<string>());

    private static RuleFixture CandidateFixtureWithInvalidGenreProjection()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureBackfillSourcePath] = fixture.Files[
                RuleFixture.FixtureBackfillSourcePath]
            .Replace(
                "genre_registry_check = \"no-registry\"",
                "genre_registry_check = \"invalid-candidate-value\"",
                StringComparison.Ordinal);
        return fixture;
    }
}
