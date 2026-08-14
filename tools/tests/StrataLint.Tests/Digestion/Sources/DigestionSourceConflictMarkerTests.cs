using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionSourceConflictMarkerTests
{
    private const string SpecPath = "docs/develop/spec/synthetic-spec.md";
    private const string TheoryPath = "docs/develop/theory/SYNTHETIC_THEORY.md";

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

    private static DigestionIngestPlan Plan(string sourcePath, string source)
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
        var snapshot = DigestionTestSupport.Snapshot((sourcePath, Encoding.UTF8.GetBytes(source)));
        return DigestionIngestor.Plan(ledger, snapshot, ledger);
    }
}
