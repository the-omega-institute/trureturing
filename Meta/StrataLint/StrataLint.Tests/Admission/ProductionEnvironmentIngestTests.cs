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
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, oldAtom)
            .Replace("atom_id: old-receipt", "atom_id: '123'", StringComparison.Ordinal)
            .Replace("migration: residual", "migration: absorbed", StringComparison.Ordinal);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallLedger(fixture, ledger, oldAtom);
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
        Assert.Contains("stale_acknowledged=0", result.Output, StringComparison.Ordinal);
        Assert.Contains("residual_open_added=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("cas_objects_written=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.Contains("DIGEST_STATUS entries=3", result.Output, StringComparison.Ordinal);
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var source = Assert.Single(written.RequireDigestionSources());
        Assert.Empty(source.AcknowledgedStale);
        Assert.Equal(3, source.Entries.Length);
        Assert.Equal(
            DigestionMigrationState.Residual,
            source.Entries.Single(static entry => entry.AtomId == "123").ProjectedStatus.Migration);
        var casBacked = source.Entries.Where(static entry => entry.AtomId != "123").ToArray();
        Assert.Equal(2, casBacked.Length);
        foreach (var entry in casBacked)
        {
            var relativePath = DigestionCasStore.RootPath
                + entry.CasRef["sha256:".Length..];
            var bytes = File.ReadAllBytes(Path.Combine(
                temporary.Path,
                relativePath.Replace('/', Path.DirectorySeparatorChar)));
            Assert.Equal(entry.CasRef, DigestionCasStore.Capture(bytes).Reference);
        }

        Assert.False(File.Exists(outputPath));
        Assert.EndsWith(
            "/123.yaml",
            Directory.EnumerateFiles(
                    Path.Combine(
                        temporary.Path,
                        BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar)),
                    "123.yaml",
                    SearchOption.AllDirectories)
                .Single()
                .Replace(Path.DirectorySeparatorChar, '/'),
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestReadsAndWritesDirectoryLayoutLedger()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(
            AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallDirectoryLedger(fixture, atomizerId, oldAtom);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
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
        Assert.Contains("residual_open_added=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath)));
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
        Assert.Equal(3, written.RequireDigestionEntries().Length);
        Assert.Equal(
            3,
            Directory.EnumerateFiles(
                    Path.Combine(
                        temporary.Path,
                        BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar)),
                    "*.yaml",
                    SearchOption.AllDirectories)
                .Count());
    }

    [Fact]
    public void IngestRejectsStructurallyInvalidLedgerWithoutWriting()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, sourceBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, atom).Replace(
            "source_id: fixture-source",
            "source_id: INVALID",
            StringComparison.Ordinal);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        InstallLedger(fixture, ledger, atom);
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
    public void IngestPerformsFirstExtractionForRegisteredEmptySource()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceText = "# Synthetic\n\n**定理 1.1(A)**。claim。\n";
        var ledger = $$"""
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: fixture-source
                path: {{GoldenCorpus.FixtureDigestionSourcePath}}
                atomizer: {{atomizerId}}
                entries: []
            ticket_index: []
            """;
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = sourceText;
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = sourceText;
        InstallLedger(fixture, ledger, existingAtom: null);
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
        var written = Assert.Single(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries());
        Assert.NotEmpty(written.AtomId);
        Assert.False(File.Exists(outputPath));
        Assert.True(Directory.Exists(Path.Combine(temporary.Path, "Meta", "Digestion")));
    }

    [Fact]
    public void IngestWarnsWhenChangedTheorySourceProducesNoNewAtoms()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldText = "# Synthetic\n\n**定理 1.1(A)**。claim。\n\n## Existing\n\nold prose。\n";
        var currentText = oldText + "\n## Added dialect\n\nnew unrecognized prose。\n";
        var oldBytes = Encoding.UTF8.GetBytes(oldText);
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, oldAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = currentText;
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = oldText;
        InstallLedger(fixture, ledger, oldAtom);
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
            "WARNING silent-zero-extraction source=fixture-source",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestCommitsReportedCoarseFallbackAndCasBlobThroughProductionEnvironment()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var malformedBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**未知 1.2(B)**。free-form source。\n");
        var malformedText = Encoding.UTF8.GetString(malformedBytes);
        var ledger = IngestLedger(atomizerId, oldAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = malformedText;
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        fixture.Files[oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan());
        fixture.Baseline[oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan());
        InstallLedger(fixture, ledger, oldAtom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var oldCasPath = Path.Combine(
            temporary.Path,
            oldCapture.RelativePath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(oldCasPath)!);
        File.WriteAllBytes(oldCasPath, oldCapture.Bytes.AsSpan());
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
        Assert.Contains("coarse_fallbacks=1", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "INGEST_FALLBACK source=fixture-source",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains("cas_objects_written=1", result.Output, StringComparison.Ordinal);
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var coarse = Assert.Single(written.RequireDigestionEntries().Where(static entry =>
            entry.AstPath == "coarse/source"));
        Assert.Equal(coarse.Fingerprints.RawSha256, coarse.CasRef);
        var coarsePath = Path.Combine(
            temporary.Path,
            DigestionCasStore.RootPath.Replace('/', Path.DirectorySeparatorChar),
            coarse.CasRef["sha256:".Length..]);
        Assert.Equal(malformedBytes, File.ReadAllBytes(coarsePath));
    }

    [Fact]
    public void IngestRollsBackNewCasObjectsWhenTheLedgerWriteFails()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, oldAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallLedger(fixture, ledger, oldAtom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(outputPath);
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
        Assert.Contains("INGEST_INVALID", result.Error, StringComparison.Ordinal);
        var casRoot = Path.Combine(
            temporary.Path,
            DigestionCasStore.RootPath.Replace('/', Path.DirectorySeparatorChar));
        Assert.False(Directory.Exists(casRoot) && Directory.EnumerateFiles(casRoot).Any());
    }

    [Fact]
    public void AtomicLedgerReplacementPreservesExistingBytesWhenCommitFails()
    {
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        var original = Encoding.UTF8.GetBytes("original ledger\n");
        var replacement = Encoding.UTF8.GetBytes("replacement ledger\n");
        File.WriteAllBytes(outputPath, original);
        string? pendingPath = null;

        var exception = Assert.Throws<IOException>(() => IngestCommand.ReplaceLedgerAtomically(
            outputPath,
            replacement,
            (pending, target) =>
            {
                pendingPath = pending;
                Assert.Equal(Path.GetDirectoryName(target), Path.GetDirectoryName(pending));
                Assert.Equal(original, File.ReadAllBytes(target));
                Assert.Equal(replacement, File.ReadAllBytes(pending));
                throw new IOException("simulated atomic commit failure");
            }));

        Assert.Equal("simulated atomic commit failure", exception.Message);
        Assert.Equal(original, File.ReadAllBytes(outputPath));
        Assert.NotNull(pendingPath);
        Assert.False(File.Exists(pendingPath));
    }

    [Fact]
    public void IngestPreservesExistingAtomIdentityInCanonicalPath()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, oldAtom).Replace(
            "atom_id: old-receipt",
            "atom_id: \"old-receipt\"",
            StringComparison.Ordinal);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallLedger(fixture, ledger, oldAtom);
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
        Assert.False(File.Exists(outputPath));
        Assert.EndsWith(
            "/old-receipt.yaml",
            Directory.EnumerateFiles(
                    Path.Combine(
                        temporary.Path,
                        BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar)),
                    "old-receipt.yaml",
                    SearchOption.AllDirectories)
                .Single()
                .Replace(Path.DirectorySeparatorChar, '/'),
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestMigratesLegacyBoundaryLedgerInOneStepAndIsIdempotent()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var legacyLedger = LegacyIngestLedger(atomizerId, oldAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallLedger(fixture, legacyLedger, oldAtom);
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
        Assert.Contains("stale_acknowledged=0", first.Output, StringComparison.Ordinal);
        Assert.Contains("residual_open_added=2", first.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", first.Output, StringComparison.Ordinal);
        Assert.False(File.Exists(outputPath));
        var migrated = BackfillInventoryLoader.LoadRoot(temporary.Path);
        Assert.All(migrated.RequireDigestionEntries(), static entry => Assert.Null(entry.Boundary));
        var migratedFiles = ReadDirectoryLedger(temporary.Path);
        foreach (var path in fixture.Files.Keys
                     .Where(BackfillInventoryLoader.IsCanonicalPath)
                     .ToArray())
        {
            fixture.Files.Remove(path);
        }
        fixture.Files.Remove(BackfillInventoryLoader.RelativePath);
        foreach (var (path, text) in migratedFiles)
        {
            fixture.Files[path] = text;
        }
        foreach (var entry in migrated.RequireDigestionEntries().Where(static entry =>
                     entry.AtomId != "old-receipt"))
        {
            var relativePath = DigestionCasStore.RootPath
                + entry.CasRef["sha256:".Length..];
            fixture.Files[relativePath] = File.ReadAllText(Path.Combine(
                temporary.Path,
                relativePath.Replace('/', Path.DirectorySeparatorChar)));
        }

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
        Assert.Contains("cas_objects_written=0", second.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=false", second.Output, StringComparison.Ordinal);
        Assert.Equal(
            migratedFiles.OrderBy(static pair => pair.Key, StringComparer.Ordinal),
            ReadDirectoryLedger(temporary.Path).OrderBy(static pair => pair.Key, StringComparer.Ordinal));
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
                cas_ref: {{atom.Fingerprints.RawSha256}}
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

    private static void InstallLedger(
        RuleFixture fixture,
        string ledger,
        DigestionAtom? existingAtom)
    {
        fixture.Files[BackfillInventoryLoader.RelativePath] = ledger;
        fixture.Baseline[BackfillInventoryLoader.RelativePath] = ledger;
        fixture.Files.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Baseline.Remove(GoldenCorpus.FixtureCasPath);
        if (existingAtom is null)
        {
            return;
        }

        var captured = DigestionCasStore.Capture(existingAtom.RawBytes.AsSpan());
        var text = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files[captured.RelativePath] = text;
        fixture.Baseline[captured.RelativePath] = text;
    }

    private static void InstallDirectoryLedger(
        RuleFixture fixture,
        string atomizerId,
        DigestionAtom atom)
    {
        var sourceMetadata = $"source_id = \"fixture-source\"\n"
            + $"path = \"{GoldenCorpus.FixtureDigestionSourcePath}\"\n"
            + $"atomizer = \"{atomizerId}\"\n"
            + "acknowledged_stale = []\n";
        var atomText = $$"""
            ast_path: {{atom.AstPath}}
            fingerprints:
              raw_sha256: {{atom.Fingerprints.RawSha256}}
              normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
            cas_ref: {{atom.Fingerprints.RawSha256}}
            coverage_gids: []
            receipts:
              coverage: []
              scribe: []
              unresolved_subitems: []
            """ + "\n";
        var sourcePath = $"{BackfillInventoryLoader.RootPath}fixture-source/source.toml";
        var atomPath = $"{BackfillInventoryLoader.RootPath}fixture-source/residual-open/old-receipt.yaml";
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files.Remove(BackfillInventoryLoader.RelativePath);
            files.Remove(GoldenCorpus.FixtureCasPath);
            files[sourcePath] = sourceMetadata;
            files[atomPath] = atomText;
            files[BackfillInventoryLoader.TicketIndexPath] = string.Empty;
        }

        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var capturedText = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files[captured.RelativePath] = capturedText;
        fixture.Baseline[captured.RelativePath] = capturedText;
    }

    private static void WriteDirectoryLedger(
        string repositoryRoot,
        IReadOnlyDictionary<string, string> files)
    {
        foreach (var (relativePath, text) in files.Where(static pair =>
                     BackfillInventoryLoader.IsCanonicalPath(pair.Key)))
        {
            var path = Path.Combine(
                repositoryRoot,
                relativePath.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, text, new UTF8Encoding(false));
        }
    }

    private static Dictionary<string, string> ReadDirectoryLedger(string repositoryRoot)
    {
        var root = Path.GetFullPath(repositoryRoot);
        var backfillRoot = Path.Combine(
            root,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar));
        var ticketIndex = Path.Combine(
            root,
            BackfillInventoryLoader.TicketIndexPath.Replace('/', Path.DirectorySeparatorChar));
        return Directory.EnumerateFiles(backfillRoot, "*", SearchOption.AllDirectories)
            .Append(ticketIndex)
            .ToDictionary(
                path => Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/'),
                path => File.ReadAllText(path, Encoding.UTF8),
                StringComparer.Ordinal);
    }

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
                cas_ref: {{atom.Fingerprints.RawSha256}}
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
