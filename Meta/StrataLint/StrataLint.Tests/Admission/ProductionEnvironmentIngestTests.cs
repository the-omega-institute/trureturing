using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestWritesOneCommitReadyLedgerUpdateAndRecomputesDigestStatus()
    {
        var fixture = new RuleFixture();
        var atomizerId = AtomizerRegistry.RegisteredIds[0];
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes).Claims);
        var ledger = IngestLedger(atomizerId, oldAtom)
            .Replace("atom_id: old-receipt", "atom_id: '123'", StringComparison.Ordinal)
            .Replace("migration: residual", "migration: absorbed", StringComparison.Ordinal);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        fixture.Files[BackfillInventoryLoader.RelativePath] = ledger;
        fixture.Baseline[BackfillInventoryLoader.RelativePath] = ledger;
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("stale_acknowledged=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("residual_open_added=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.Contains("DIGEST_STATUS entries=3", result.Output, StringComparison.Ordinal);
        var writtenText = File.ReadAllText(outputPath);
        var written = BackfillInventoryLoader.Load(writtenText);
        var source = Assert.Single(written.RequireDigestionSources());
        Assert.Equal(["123"], source.AcknowledgedStale.ToArray());
        Assert.Equal(3, source.Entries.Length);
        Assert.Equal(
            DigestionMigrationState.Residual,
            source.Entries.Single(static entry => entry.AtomId == "123").ProjectedStatus.Migration);
        Assert.Contains("atom_id: '123'", writtenText, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRejectsStructurallyInvalidLedgerWithoutWriting()
    {
        var fixture = new RuleFixture();
        var atomizerId = AtomizerRegistry.RegisteredIds[0];
        var sourceBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, sourceBytes).Claims);
        var ledger = IngestLedger(atomizerId, atom).Replace(
            "source_id: fixture-source",
            "source_id: INVALID",
            StringComparison.Ordinal);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Files[BackfillInventoryLoader.RelativePath] = ledger;
        fixture.Baseline[BackfillInventoryLoader.RelativePath] = ledger;
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("invalid source_id: INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(ledger, File.ReadAllText(outputPath));
    }

    [Fact]
    public void IngestPreservesExactNoncanonicalStaleReceiptRepresentation()
    {
        var fixture = new RuleFixture();
        var atomizerId = AtomizerRegistry.RegisteredIds[0];
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes).Claims);
        var ledger = IngestLedger(atomizerId, oldAtom).Replace(
            "atom_id: old-receipt",
            "atom_id: \"old-receipt\"",
            StringComparison.Ordinal);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        fixture.Files[BackfillInventoryLoader.RelativePath] = ledger;
        fixture.Baseline[BackfillInventoryLoader.RelativePath] = ledger;
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            "atom_id: \"old-receipt\"",
            File.ReadAllText(outputPath),
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestMigratesLegacyBoundaryLedgerInOneStepAndIsIdempotent()
    {
        var fixture = new RuleFixture();
        var atomizerId = AtomizerRegistry.RegisteredIds[0];
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes).Claims);
        var legacyLedger = LegacyIngestLedger(atomizerId, oldAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        fixture.Files[BackfillInventoryLoader.RelativePath] = legacyLedger;
        fixture.Baseline[BackfillInventoryLoader.RelativePath] = legacyLedger;
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, legacyLedger, new UTF8Encoding(false));
        var firstEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var first = firstEnvironment.Ingest(["--base", "baseline"]);

        Assert.True(first.Success, first.Error);
        Assert.Contains("stale_acknowledged=1", first.Output, StringComparison.Ordinal);
        Assert.Contains("residual_open_added=2", first.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", first.Output, StringComparison.Ordinal);
        var migratedText = File.ReadAllText(outputPath);
        Assert.DoesNotContain("boundary:", migratedText, StringComparison.Ordinal);
        var migrated = BackfillInventoryLoader.Load(migratedText);
        Assert.All(migrated.RequireDigestionEntries(), static entry => Assert.Null(entry.Boundary));
        fixture.Files[BackfillInventoryLoader.RelativePath] = migratedText;
        var secondEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var second = secondEnvironment.Ingest(["--base", "baseline"]);

        Assert.True(second.Success, second.Error);
        Assert.Contains("stale_acknowledged=0", second.Output, StringComparison.Ordinal);
        Assert.Contains("residual_open_added=0", second.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=false", second.Output, StringComparison.Ordinal);
        Assert.Equal(migratedText, File.ReadAllText(outputPath));
    }

    private static string IngestLedger(string atomizerId, DigestionAtom atom) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: fixture-source
            path: {{GoldenCorpus.FixtureDigestionSourcePath}}
            atomizer: {{atomizerId}}
            acknowledged_stale: []
            entries:
              - atom_id: old-receipt
                ast_path: {{atom.AstPath}}
                fingerprints:
                  raw_sha256: {{atom.Fingerprints.RawSha256}}
                  normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
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

    private static string LegacyIngestLedger(string atomizerId, DigestionAtom atom) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: fixture-source
            path: {{GoldenCorpus.FixtureDigestionSourcePath}}
            atomizer: {{atomizerId}}
            entries:
              - atom_id: old-receipt
                boundary:
                  ast_path: {{atom.AstPath}}
                  start_byte: {{atom.StartByte}}
                  end_byte: {{atom.EndByte}}
                fingerprints:
                  raw_sha256: {{atom.Fingerprints.RawSha256}}
                  normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
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
}
