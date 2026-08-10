using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class EchoVerifyCommandTests
{
    private const string Summary = "# Echo Residual Summary\n\n- unresolved_subitems: 1\n";

    [Fact]
    public void ContentAddressedBlockRendersTheResidualProjection()
    {
        var rendered = EchoResidualBlock.Render(Summary);

        Assert.StartsWith(
            "<!-- echo-residual-summary:v3 residual=sha256:05f4f3c3989efd7578fb7fdf6716b7a76aed13b8e840bd5a3fd624b86dd9bca9 -->\n",
            rendered,
            StringComparison.Ordinal);
        Assert.Equal(Summary, rendered[(rendered.IndexOf('\n') + 1)..]);
    }

    [Fact]
    public void ShardDigestBindsTheSourceId()
    {
        const string body = "# body\n";
        var sourceA = EchoResidualBlock.RenderShard("source-a", body);
        var sourceB = EchoResidualBlock.RenderShard("source-b", body);

        Assert.NotEqual(sourceA, sourceB);
        Assert.True(EchoResidualBlock.VerifyShard("source-a", sourceA));
        Assert.False(EchoResidualBlock.VerifyShard("source-b", sourceA));
    }

    [Fact]
    public void AggregateAndShardsPreserveSyntheticResidualDistribution()
    {
        var evaluation = new DigestionLedgerEvaluation([
            Entry("source-a", "atom-a", "shared"),
            Entry("source-a", "atom-b", "shared", "a-only"),
            Entry("source-b", "atom-c", "shared", "b-only"),
        ], []);

        var aggregate = DigestResidualSummary.Render(evaluation);
        var shards = DigestResidualSummary.RenderShards(evaluation);

        Assert.Equal(
            Metric(aggregate, "unresolved_subitems"),
            shards.Values.Sum(shard => Metric(shard, "unresolved_subitems")));
        Assert.Equal(
            Metric(aggregate, "mother_residual_atom_ids"),
            shards.Values.Sum(shard => Metric(shard, "mother_residual_atom_ids")));
        Assert.Equal(1, Metric(aggregate, "shared_residue_names"));
        Assert.Equal(3, Metric(aggregate, "host_atoms"));
        Assert.Contains("`shared` (2 volumes, 3 host atoms)", aggregate, StringComparison.Ordinal);
        Assert.Equal(2, CountOccurrences(shards["Generated/echo-residuals/source-a.md"], "  - `shared`"));
        Assert.Equal(1, CountOccurrences(shards["Generated/echo-residuals/source-b.md"], "  - `shared`"));
    }

    [Fact]
    public void StructureCheckAcceptsCompleteShardSet()
    {
        using var temporary = new TemporaryDirectory();
        WriteShard(temporary.Path, "source-a", "# stale a\n");
        WriteShard(temporary.Path, "source-b", "# stale b\n");

        var result = EchoVerifyCommand.CheckStructure(temporary.Path, ["source-a", "source-b"]);

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void StructureCheckRejectsMissingShard()
    {
        using var temporary = new TemporaryDirectory();
        WriteShard(temporary.Path, "source-a", "# stale a\n");

        var result = EchoVerifyCommand.CheckStructure(temporary.Path, ["source-a", "source-b"]);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("missing=source-b.md", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void StructureCheckRejectsExtraShard()
    {
        using var temporary = new TemporaryDirectory();
        WriteShard(temporary.Path, "source-a", "# stale a\n");
        WriteShard(temporary.Path, "extra", "# stale extra\n");

        var result = EchoVerifyCommand.CheckStructure(temporary.Path, ["source-a"]);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("extra=extra.md", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void StructureCheckRejectsLegacyAggregateAlongsideShards()
    {
        using var temporary = new TemporaryDirectory();
        WriteShard(temporary.Path, "source-a", "# stale a\n");
        Directory.CreateDirectory(Path.Combine(temporary.Path, "Generated"));
        File.WriteAllText(Path.Combine(temporary.Path, "Generated", "echo-residual-summary.md"), "legacy");

        var result = EchoVerifyCommand.CheckStructure(temporary.Path, ["source-a"]);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("legacy aggregate exists", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void StructureCheckRejectsShardReplayedAtDifferentSourcePath()
    {
        using var temporary = new TemporaryDirectory();
        var directory = Path.Combine(temporary.Path, "Generated", "echo-residuals");
        Directory.CreateDirectory(directory);
        File.WriteAllText(
            Path.Combine(directory, "source-b.md"),
            EchoResidualBlock.RenderShard("source-a", "# stale a\n"));

        var result = EchoVerifyCommand.CheckStructure(temporary.Path, ["source-b"]);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("invalid shard source-b.md", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void StructureCheckRejectsMissingShardDirectory()
    {
        using var temporary = new TemporaryDirectory();

        var result = EchoVerifyCommand.CheckStructure(temporary.Path, ["source-a"]);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("shard directory does not exist", result.Error, StringComparison.Ordinal);
    }

    private static int Metric(string content, string name)
    {
        var line = content.Split('\n').First(candidate =>
            candidate.StartsWith($"- {name}:", StringComparison.Ordinal));
        return int.Parse(line[(line.IndexOf(':') + 1)..]);
    }

    private static int CountOccurrences(string content, string value) =>
        content.Split(value, StringSplitOptions.None).Length - 1;

    private static void WriteShard(string root, string sourceId, string body)
    {
        var directory = Path.Combine(root, "Generated", "echo-residuals");
        Directory.CreateDirectory(directory);
        File.WriteAllText(
            Path.Combine(directory, sourceId + ".md"),
            EchoResidualBlock.RenderShard(sourceId, body));
    }

    private static DigestionEntryEvaluation Entry(
        string sourceId,
        string atomId,
        params string[] residuals)
    {
        var status = new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed);
        var entry = new DigestionLedgerEntry(
            sourceId,
            "synthetic.md",
            "synthetic-v1",
            atomId,
            "synthetic/path",
            null,
            new DigestionFingerprints("sha256:synthetic", "sha256:synthetic"),
            [],
            new DigestionReceipts([], [], [], [], null),
            status,
            null,
            "sha256:synthetic");
        return new DigestionEntryEvaluation(
            entry,
            DigestionReceiptAlignment.Seen,
            status,
            false,
            residuals.Select(static residual =>
                new DigestionGap("unresolved-subitem", residual)).ToImmutableArray());
    }
}
