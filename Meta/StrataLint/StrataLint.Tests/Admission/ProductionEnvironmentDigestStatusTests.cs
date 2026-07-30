using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void DigestStatusReportsCasSeenAcrossNormalizedSourceRewrite()
    {
        var fixture = new RuleFixture();
        var atomizerId = AtomizerRegistry.RegisteredIds[0];
        var ledgerBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\r\n\r\n**定理 1.1(Test)**。claim。\r\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, ledgerBytes).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Files.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Files[captured.RelativePath] = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files["Meta/BACKFILL.yaml"] = $$"""
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: fixture-source
                path: {{GoldenCorpus.FixtureDigestionSourcePath}}
                atomizer: {{atomizerId}}
                acknowledged_stale: []
                entries:
                  - atom_id: normalized-receipt
                    ast_path: {{atom.AstPath}}
                    fingerprints:
                      raw_sha256: {{atom.Fingerprints.RawSha256}}
                      normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                    cas_ref: {{captured.Reference}}
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
                    status:
                      migration: residual
                      truth: open
            ticket_index: []
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
        Assert.Contains("\"atom_id\": \"fixture-atom\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"code\": \"boundary-not-reproducible\"", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusResidualSummaryUsesMachineDerivedUnresolvedSubitemGaps()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[BackfillInventoryLoader.RelativePath] = fixture.Files[BackfillInventoryLoader.RelativePath]
            .Replace(
                "          unresolved_subitems: []",
                "          unresolved_subitems:\n            - zeta-residual\n            - alpha-residual",
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
        Assert.Contains("- `fixture-atom` (2)", result.Output, StringComparison.Ordinal);
        Assert.True(
            result.Output.IndexOf("`alpha-residual`", StringComparison.Ordinal)
                < result.Output.IndexOf("`zeta-residual`", StringComparison.Ordinal));
        Assert.DoesNotContain("boundary-not-reproducible", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusReportsHistoricalAndCurrentCasReceiptsAsSeen()
    {
        var fixture = new RuleFixture();
        var atomizerId = AtomizerRegistry.RegisteredIds[0];
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes).Claims);
        var baselineLedger = IngestLedger(atomizerId, oldAtom);
        var baselineDocument = BackfillInventoryLoader.Load(baselineLedger);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var planningSnapshot = Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes),
            [oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan()),
        }));
        var plan = DigestionIngestor.Plan(baselineDocument, planningSnapshot, baselineDocument);
        var candidateLedger = Encoding.UTF8.GetString(
            BackfillInventoryWriter.Write(plan.Document).AsSpan());
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        fixture.Files[BackfillInventoryLoader.RelativePath] = candidateLedger;
        fixture.Baseline[BackfillInventoryLoader.RelativePath] = baselineLedger;
        fixture.Files.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Baseline.Remove(GoldenCorpus.FixtureCasPath);
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

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"alignment\": \"seen\"", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("stale-receipt-not-deletable", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusFailsClosedWhenProjectedStatusWasHandwrittenIncorrectly()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        const string expected = "          migration: partial\n          truth: closed";
        const string falseProjection = "          migration: absorbed\n          truth: closed";
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"].Replace(
            expected,
            falseProjection,
            StringComparison.Ordinal);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(Array.Empty<string>());

        Assert.False(result.Success);
        Assert.Contains("handwritten status", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusFailsClosedWhenScribeVerificationFails()
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
            new FakeScribeEmissionVerifier(null));

        var result = environment.DigestStatus(Array.Empty<string>());

        Assert.False(result.Success);
        Assert.Contains("Scribe emission verification failed", result.Error, StringComparison.Ordinal);
    }
}
