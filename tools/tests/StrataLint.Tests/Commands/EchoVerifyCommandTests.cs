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
    }

    [Fact]
    public void EchoTemplatePolicyRejectsMissingResidualVocabulary()
    {
        var findings = EchoTemplatePolicy.Validate("# Statement Echo\n");

        Assert.Contains(findings, finding =>
            finding.Contains("Remark-closure guard", StringComparison.Ordinal));
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

    private static int Metric(string content, string name)
    {
        var line = content.Split('\n').First(candidate =>
            candidate.StartsWith($"- {name}:", StringComparison.Ordinal));
        return int.Parse(line[(line.IndexOf(':') + 1)..]);
    }

    private static int CountOccurrences(string content, string value) =>
        content.Split(value, StringSplitOptions.None).Length - 1;

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
            new DigestionFingerprints("sha256:synthetic", "sha256:synthetic"),
            [],
            new DigestionReceipts([], [], [], [], null),
            status,
            "sha256:synthetic");
        return new DigestionEntryEvaluation(
            entry,
            DigestionReceiptAlignment.Seen,
            status,
            false,
            residuals.Select(static residual =>
                new DigestionGap(
                    "unresolved-subitem",
                    residual,
                    DigestionGapSeverity.NonFatal)).ToImmutableArray());
    }
}
