using System;
using System.Text;
using Trureturing.Truth;
using Xunit;

namespace Trureturing.Truth.Tests;

public sealed class TruthReleaseSourceSnapshotJsonTests
{
    private const string ValidSnapshot = """
        {
          "schema": "source-snapshot",
          "source_repo": "the-omega-institute/trureturing",
          "source_commit": "1111111111111111111111111111111111111111",
          "source_tree": "2222222222222222222222222222222222222222",
          "lean_toolchain": "leanprover/lean4:v4.24.0",
          "mathlib_rev": "3333333333333333333333333333333333333333",
          "producer_package_commit": "4444444444444444444444444444444444444444",
          "truth_graph_sha256": "sha256:5555555555555555555555555555555555555555555555555555555555555555",
          "raw_lean_report_sha256": "sha256:6666666666666666666666666666666666666666666666666666666666666666",
          "dag_md_sha256": "sha256:7777777777777777777777777777777777777777777777777777777777777777",
          "declarations_sha256": "sha256:9999999999999999999999999999999999999999999999999999999999999999"
        }
        """;

    private const string LastProperty =
        "\"declarations_sha256\": \"sha256:9999999999999999999999999999999999999999999999999999999999999999\"";

    [Fact]
    public void ReadsTheExactSnapshotShape()
    {
        var snapshot = SourceSnapshotJsonReader.Read(Encoding.UTF8.GetBytes(ValidSnapshot));

        Assert.Equal("source-snapshot", snapshot.Schema);
        Assert.Equal("1111111111111111111111111111111111111111", snapshot.SourceCommit);
        Assert.Equal("2222222222222222222222222222222222222222", snapshot.SourceTree);
        Assert.Equal(
            "sha256:5555555555555555555555555555555555555555555555555555555555555555",
            snapshot.TruthGraphSha256);
        Assert.Equal(
            "sha256:9999999999999999999999999999999999999999999999999999999999999999",
            snapshot.DeclarationsSha256);
    }

    [Theory]
    [InlineData("\"source-snapshot\"", "\"source-snapshot.v2\"")]
    [InlineData("\"source-snapshot\"", "\"source-snapshot.v1\"")]
    [InlineData("\"source_commit\": \"1111111111111111111111111111111111111111\"", "\"source_commit\": \"not-a-git-id\"")]
    [InlineData("\"truth_graph_sha256\": \"sha256:5555555555555555555555555555555555555555555555555555555555555555\"", "\"truth_graph_sha256\": \"sha256:bad\"")]
    public void RejectsInvalidSchemaAndIdentityFormats(string original, string replacement)
    {
        var json = ValidSnapshot.Replace(original, replacement, StringComparison.Ordinal);
        Assert.Throws<FormatException>(() => SourceSnapshotJsonReader.Read(Encoding.UTF8.GetBytes(json)));
    }

    [Fact]
    public void RejectsMixedGitObjectFormats()
    {
        var json = ValidSnapshot.Replace(
            "\"source_tree\": \"2222222222222222222222222222222222222222\"",
            "\"source_tree\": \"2222222222222222222222222222222222222222222222222222222222222222\"",
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => SourceSnapshotJsonReader.Read(Encoding.UTF8.GetBytes(json)));
    }

    [Fact]
    public void RejectsAdditionalProperties()
    {
        var json = ValidSnapshot.Replace(
            LastProperty,
            LastProperty + ", \"extra\": true",
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => SourceSnapshotJsonReader.Read(Encoding.UTF8.GetBytes(json)));
    }

    [Theory]
    [InlineData("\"frozen_ledger_head_hash\": \"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"")]
    [InlineData("\"frozen_ledger_sequence\": 42")]
    public void RejectsRetiredFrozenLedgerFields(string retiredProperty)
    {
        var json = ValidSnapshot.Replace(
            LastProperty,
            LastProperty + ", " + retiredProperty,
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => SourceSnapshotJsonReader.Read(Encoding.UTF8.GetBytes(json)));
    }

    [Fact]
    public void RejectsADigestionDigestInTheSourceSnapshotContract()
    {
        var json = ValidSnapshot.Replace(
            LastProperty,
            LastProperty + ", \"residual_frontier_sha256\": \"sha256:" + new string('8', 64) + "\"",
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => SourceSnapshotJsonReader.Read(Encoding.UTF8.GetBytes(json)));
    }

    [Fact]
    public void RejectsMissingProperties()
    {
        var json = ValidSnapshot.Replace(
            "  \"lean_toolchain\": \"leanprover/lean4:v4.24.0\",\n",
            string.Empty,
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => SourceSnapshotJsonReader.Read(Encoding.UTF8.GetBytes(json)));
    }

    [Fact]
    public void RejectsDuplicateProperties()
    {
        var json = ValidSnapshot.Replace(
            LastProperty,
            LastProperty + ", \"source_commit\": \"1111111111111111111111111111111111111111\"",
            StringComparison.Ordinal);

        Assert.Throws<FormatException>(() => SourceSnapshotJsonReader.Read(Encoding.UTF8.GetBytes(json)));
    }
}
