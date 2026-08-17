using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionSourceConflictMarkerTests
{
    private const string CanonicalSpecPath = "docs/develop/spec/golden-ledger-repo-spec.md";
    private const string SpecPath = "docs/develop/spec/synthetic-spec.md";
    private const string TheoryPath = "docs/develop/theory/SYNTHETIC_THEORY.md";

    private const string E968SpecConflictExcerpt = """
        <!-- BACKFILL_ENTRY_ACCEPTANCE -->
        Digestion ledger source text from the rejected candidate.
        <<<<<<< HEAD
        ## 11.22 orchestration
        =======
        >>>>>>> origin/dev
        ## 11.23 machine checks
        """;

    [Theory]
    [InlineData(SpecPath, "<<<<<<< HEAD")]
    [InlineData(TheoryPath, "=======")]
    [InlineData(TheoryPath, ">>>>>>> origin/dev")]
    public void IngestRejectsConflictMarkersWithDiagnosticCodeAndSourceLine(
        string sourcePath,
        string marker)
    {
        var source = $"# Synthetic source\nclean preface\n{marker}\n## Claim 1.1\nclean claim\n";

        var error = Assert.Throws<FormatException>(() => Plan(sourcePath, source));

        Assert.Contains("INGEST-CONFLICT-MARKER-001", error.Message, StringComparison.Ordinal);
        Assert.Contains($"{sourcePath}:3", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CleanDigestionSourceStillPasses()
    {
        var plan = Plan(SpecPath, "# Synthetic source\n\n## Claim 1.1\nclean claim\n");

        Assert.NotEmpty(plan.Document.RequireDigestionEntries());
    }

    [Fact]
    public void SeparatorTextInsideALineIsNotAConflictMarker()
    {
        var plan = Plan(
            TheoryPath,
            "# Synthetic source\n\n## Claim 1.1\nleft ======= right\n");

        Assert.NotEmpty(plan.Document.RequireDigestionEntries());
    }

    [Fact]
    public void AdmissionRejectsTheE968SpecConflictWithoutCallingIngestPlan()
    {
        var findings = AdmissionFindings(Encoding.UTF8.GetBytes(E968SpecConflictExcerpt));

        var finding = Assert.Single(findings, static message =>
            message.Contains("INGEST-CONFLICT-MARKER-001", StringComparison.Ordinal));
        Assert.Contains($"{CanonicalSpecPath}:3", finding, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRejectsConflictMarkerOnFirstLineAfterUtf8Bom()
    {
        var source = Encoding.UTF8.GetPreamble()
            .Concat(Encoding.UTF8.GetBytes("<<<<<<< HEAD\nclean tail\n"))
            .ToArray();

        var error = Assert.Throws<FormatException>(() => Plan(SpecPath, source));

        Assert.Contains("INGEST-CONFLICT-MARKER-001", error.Message, StringComparison.Ordinal);
        Assert.Contains($"{SpecPath}:1", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRejectsDiff3BaseMarker()
    {
        var error = Assert.Throws<FormatException>(() => Plan(
            TheoryPath,
            "clean preface\n||||||| merge-base\nclean tail\n"));

        Assert.Contains("INGEST-CONFLICT-MARKER-001", error.Message, StringComparison.Ordinal);
        Assert.Contains($"{TheoryPath}:2", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AlignScribeReceiptRejectsConflictMarkedSourceWithoutChangingLedger()
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal)
        {
            [RuleFixture.FixtureDigestionSourcePath] = "<<<<<<< HEAD\nconflicted source\n",
        };
        files = DirectoryLedgerTestSupport.Project(files);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = CoverWorld.Environment(temporary.Path, inputs, files)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains("INGEST-CONFLICT-MARKER-001", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    private static DigestionIngestPlan Plan(string sourcePath, string source)
        => Plan(sourcePath, Encoding.UTF8.GetBytes(source));

    private static DigestionIngestPlan Plan(string sourcePath, byte[] sourceBytes)
    {
        var ledger = DigestionTestSupport.Document(
            AtomizerRegistry.GenericId,
            [],
            "synthetic-source",
            sourcePath,
            GenreRegistryCheck.Collected([]));
        var snapshot = DigestionTestSupport.Snapshot((sourcePath, sourceBytes));
        return DigestionIngestor.Plan(ledger, snapshot, ledger);
    }

    private static string[] AdmissionFindings(byte[] sourceBytes)
    {
        var firstLineEnd = Array.IndexOf(sourceBytes, (byte)'\n');
        var receiptBytes = sourceBytes[..(firstLineEnd >= 0 ? firstLineEnd + 1 : sourceBytes.Length)];
        var fingerprints = DigestionFingerprint.Compute(receiptBytes);
        var cas = DigestionCasStore.Capture(receiptBytes);
        var ledgerEntry = new DigestionLedgerEntry(
            "canonical-spec",
            CanonicalSpecPath,
            AtomizerRegistry.NoAtomizerId,
            "canonical-spec-fixture",
            "manual/spec",
            new DigestionBoundary("manual/spec", 0, receiptBytes.Length),
            fingerprints,
            [],
            new DigestionReceipts([], [], [], [], null),
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            cas.Reference);
        var ledger = DigestionTestSupport.Document(
            AtomizerRegistry.NoAtomizerId,
            [ledgerEntry],
            "canonical-spec",
            CanonicalSpecPath);
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [CanonicalSpecPath] = Encoding.UTF8.GetString(sourceBytes),
            [cas.RelativePath] = Encoding.UTF8.GetString(cas.Bytes.AsSpan()),
        };
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, ledger);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(CoverWorld.Raw(files))).Snapshot;

        return BackfillInventoryRule.EvaluateDocument(
                new BackfillInventoryValidationContext(
                    snapshot,
                    snapshot,
                    policy,
                    DigestionTestSupport.AcceptedLean(Array.Empty<string>()),
                    null),
                ledger)
            .Select(static finding => finding.Message)
            .ToArray();
    }
}
