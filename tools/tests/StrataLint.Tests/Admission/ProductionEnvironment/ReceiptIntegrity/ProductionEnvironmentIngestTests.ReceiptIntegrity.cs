using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestRejectsInputReceiptIntegrityFailureBeforeProjectingStatuses()
    {
        using var temporary = new TemporaryDirectory();
        var environment = ReceiptIntegrityStatusProjectionEnvironment(
            temporary.Path,
            includeInputMismatch: true);

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.StartsWith(
            "INGEST_INVALID digest status is invalid:",
            result.Error,
            StringComparison.Ordinal);
        Assert.Contains(
            "stable-generation:coverage-receipt-mismatch",
            result.Error,
            StringComparison.Ordinal);
        // This absence binds the prewrite gate: deleting that call lets status projection
        // create the stale finding before rejection. It does not bind later gates or a disk write.
        Assert.DoesNotContain(
            "stale receipts are not acknowledged: old-generation",
            result.Error,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRejectsReceiptIntegrityFailureCreatedByStatusProjection()
    {
        using var temporary = new TemporaryDirectory();
        var environment = ReceiptIntegrityStatusProjectionEnvironment(
            temporary.Path,
            includeInputMismatch: false);

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.False(result.Success);
        // This prefix binds the postwrite receipt-integrity gate: deleting that call falls
        // through to SL-016's distinct diagnostic. It does not bind SL-016 or the atomic writer.
        Assert.StartsWith(
            "INGEST_INVALID digest status is invalid:",
            result.Error,
            StringComparison.Ordinal);
        Assert.Contains(
            "stale receipts are not acknowledged: old-generation",
            result.Error,
            StringComparison.Ordinal);
    }

    private static ProductionCliEnvironment ReceiptIntegrityStatusProjectionEnvironment(
        string repositoryRoot,
        bool includeInputMismatch)
    {
        const string coverageGid = "D5/S0/Carrier/Ring";
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。old。\n\n**定理 1.2(B)**。stable。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。stable。\n");
        var oldAtoms = AtomizerRegistry.Atomize(
            atomizerId,
            oldBytes,
            DigestionTestSupport.Rules).Claims;
        var oldGeneration = oldAtoms.Single(static atom => atom.AstPath.Contains("1.1", StringComparison.Ordinal));
        var stableGeneration = oldAtoms.Single(static atom => atom.AstPath.Contains("1.2", StringComparison.Ordinal));
        var stableEntry = DigestionTestSupport.Entry(
            stableGeneration,
            "stable-generation",
            atomizerId,
            coverageGids: includeInputMismatch ? [coverageGid] : [],
            receipts: includeInputMismatch
                ? new DigestionReceipts(
                    [
                        new DigestionCoverageReceipt(
                            coverageGid,
                            stableGeneration.Fingerprints.RawSha256,
                            "sha256:" + new string('c', 64)),
                    ],
                    [],
                    [],
                    [],
                    null)
                : null,
            sourceId: "fixture-source",
            sourcePath: RuleFixture.FixtureDigestionSourcePath);
        var document = DigestionTestSupport.Document(
            atomizerId,
            [
                DigestionTestSupport.Entry(
                    oldGeneration,
                    "old-generation",
                    atomizerId,
                    migration: DigestionMigrationState.Partial,
                    sourceId: "fixture-source",
                    sourcePath: RuleFixture.FixtureDigestionSourcePath),
                stableEntry,
            ],
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            GenreRegistryCheck.Collected([]));
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallProjectedLedger(fixture, document, existingAtom: null);
        var source = Assert.Single(document.RequireDigestionSources());
        var baselineDocument = document.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries.Select(entry => entry.AtomId == "old-generation"
                    ? entry with
                    {
                        ProjectedStatus = new DigestionStatus(
                            DigestionMigrationState.Residual,
                            DigestionTruthState.Open),
                    }
                    : entry).ToImmutableArray(),
            },
        ]);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, baselineDocument);
        foreach (var atom in oldAtoms)
        {
            var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
            var text = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
            fixture.Files[captured.RelativePath] = text;
            fixture.Baseline[captured.RelativePath] = text;
        }

        WriteDirectoryLedger(repositoryRoot, fixture.Files);
        return new ProductionCliEnvironment(
            repositoryRoot,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
    }
}
