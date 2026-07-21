using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class EchoVerifyCommandTests
{
    private const string BaseCommit = "git-sha1:2222222222222222222222222222222222222222";
    private const string OtherBaseCommit = "git-sha1:3333333333333333333333333333333333333333";
    private const string Summary = "# Echo Residual Summary\n\n- unresolved_subitems: 1\n";

    [Fact]
    public void SnapshotBoundBlockRoundTripsAsExactProjectionFile()
    {
        var expected = EchoResidualBlock.Render(Summary, BaseCommit);

        var error = EchoResidualBlock.Verify(
            Encoding.UTF8.GetBytes(expected),
            Encoding.UTF8.GetBytes(expected));

        Assert.Null(error);
        Assert.Equal(
            $"""
            <!-- echo-residual-summary:v2 base={BaseCommit} -->
            {Summary}<!-- /echo-residual-summary:v2 -->
            """ + "\n",
            expected);
    }

    [Fact]
    public void MarkerTextInsideResidualDataDoesNotBreakExactProjectionVerification()
    {
        const string collisionSummary = """
            # Echo Residual Summary

            - `<!-- echo-residual-summary:v2 synthetic -->`
            - `<!-- /echo-residual-summary:v2 -->`

            """;
        var expected = EchoResidualBlock.Render(collisionSummary, BaseCommit);

        var error = EchoResidualBlock.Verify(
            Encoding.UTF8.GetBytes(expected),
            Encoding.UTF8.GetBytes(expected));

        Assert.Null(error);
    }

    [Theory]
    [InlineData("hand-edited", "unresolved_subitems: 1", "unresolved_subitems: 2")]
    [InlineData("stale-snapshot", BaseCommit, OtherBaseCommit)]
    public void HandEditedOrStaleBlockFailsByteVerification(
        string _,
        string original,
        string replacement)
    {
        var expected = EchoResidualBlock.Render(Summary, BaseCommit);
        var candidate = expected.Replace(original, replacement, StringComparison.Ordinal);

        var error = EchoResidualBlock.Verify(
            Encoding.UTF8.GetBytes(candidate),
            Encoding.UTF8.GetBytes(expected));

        Assert.Equal("candidate block does not byte-match the derived residual summary", error);
    }

    [Fact]
    public void MissingBlockFailsClosed()
    {
        var expected = EchoResidualBlock.Render(Summary, BaseCommit);

        var error = EchoResidualBlock.Verify(
            "review prose only\n"u8,
            Encoding.UTF8.GetBytes(expected));

        Assert.Equal("candidate contains no echo residual summary block", error);
    }

    [Fact]
    public void DuplicateBlockFailsClosed()
    {
        var expected = EchoResidualBlock.Render(Summary, BaseCommit);

        var error = EchoResidualBlock.Verify(
            Encoding.UTF8.GetBytes(expected + expected),
            Encoding.UTF8.GetBytes(expected));

        Assert.Equal("candidate contains multiple echo residual summary blocks", error);
    }

    [Theory]
    [InlineData("D5/Synthetic/EchoInput.lean", true)]
    [InlineData("Blueprint/Synthetic/EchoInput.scribe.cs", true)]
    [InlineData("Meta/BACKFILL.yaml", true)]
    [InlineData("Meta/Digestion/atoms/sha256/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", true)]
    [InlineData("docs/develop/" + "theory/SYNTHETIC.md", true)]
    [InlineData("Generated/echo-residual-summary.md", true)]
    [InlineData("Blueprint/Synthetic/EchoInput.md", false)]
    [InlineData("README.md", false)]
    public void AffectedPathsMatchResidualInputs(string path, bool expected)
    {
        Assert.Equal(expected, EchoVerifyCommand.IsAffected(RawChangeSet.Create([path])));
    }
}
