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
        using var temporary = new TemporaryDirectory();
        var ledgerPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(ledgerPath)!);
        var before = Encoding.UTF8.GetBytes(inputs.Ledger);
        File.WriteAllBytes(ledgerPath, before);

        var result = CoverWorld.Environment(temporary.Path, inputs, files)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains("INGEST-CONFLICT-MARKER-001", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, File.ReadAllBytes(ledgerPath));
    }

    private static DigestionIngestPlan Plan(string sourcePath, string source)
        => Plan(sourcePath, Encoding.UTF8.GetBytes(source));

    private static DigestionIngestPlan Plan(string sourcePath, byte[] sourceBytes)
    {
        var ledger = BackfillInventoryLoader.Load($$"""
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: synthetic-source
                path: {{sourcePath}}
                atomizer: {{AtomizerRegistry.GenericId}}
                entries: []
            ticket_index: []
            """);
        var snapshot = DigestionTestSupport.Snapshot((sourcePath, sourceBytes));
        return DigestionIngestor.Plan(ledger, snapshot, ledger);
    }

    private static string[] AdmissionFindings(byte[] sourceBytes)
    {
        var firstLineEnd = Array.IndexOf(sourceBytes, (byte)'\n');
        var receiptBytes = sourceBytes[..(firstLineEnd >= 0 ? firstLineEnd + 1 : sourceBytes.Length)];
        var fingerprints = DigestionFingerprint.Compute(receiptBytes);
        var cas = DigestionCasStore.Capture(receiptBytes);
        var ledgerText = $$"""
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: canonical-spec
                path: {{CanonicalSpecPath}}
                atomizer: {{AtomizerRegistry.NoAtomizerId}}
                entries:
                  - atom_id: canonical-spec-fixture
                    boundary:
                      ast_path: manual/spec
                      start_byte: 0
                      end_byte: {{receiptBytes.Length}}
                    fingerprints:
                      raw_sha256: {{fingerprints.RawSha256}}
                      normalized_sha256: {{fingerprints.NormalizedSha256}}
                    cas_ref: {{cas.Reference}}
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
        var ledger = BackfillInventoryLoader.Load(ledgerText);
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
        var snapshot = DigestionTestSupport.Snapshot(
            (CanonicalSpecPath, sourceBytes),
            (BackfillInventoryLoader.RelativePath, Encoding.UTF8.GetBytes(ledgerText)),
            (cas.RelativePath, cas.Bytes.ToArray()));

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
