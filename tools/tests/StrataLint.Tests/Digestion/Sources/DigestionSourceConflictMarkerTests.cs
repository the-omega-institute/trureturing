using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
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
}
