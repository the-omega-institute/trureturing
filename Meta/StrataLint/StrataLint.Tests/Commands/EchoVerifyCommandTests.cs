using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class EchoVerifyCommandTests
{
    private const string Summary = "# Echo Residual Summary\n\n- unresolved_subitems: 1\n";

    [Fact]
    public void ContentAddressedBlockRoundTripsAsExactProjectionFile()
    {
        var expected = EchoResidualBlock.Render(Summary);

        var error = EchoResidualBlock.Verify(
            Encoding.UTF8.GetBytes(expected),
            Encoding.UTF8.GetBytes(expected));

        Assert.Null(error);
        Assert.StartsWith(
            "<!-- echo-residual-summary:v3 residual=sha256:05f4f3c3989efd7578fb7fdf6716b7a76aed13b8e840bd5a3fd624b86dd9bca9 -->\n",
            expected,
            StringComparison.Ordinal);
        Assert.Equal(Summary, expected[(expected.IndexOf('\n') + 1)..]);
    }

    [Fact]
    public void ContentAddressedBlockTreatsMarkerTextInResidualBodyAsOpaque()
    {
        var summaryWithMarkerText = Summary
            + "<!-- echo-residual-summary: this is residual prose, not a header -->\n";
        var expected = EchoResidualBlock.Render(summaryWithMarkerText);

        var error = EchoResidualBlock.Verify(
            Encoding.UTF8.GetBytes(expected),
            Encoding.UTF8.GetBytes(expected));

        Assert.Null(error);
        Assert.Contains(
            "<!-- echo-residual-summary: this is residual prose, not a header -->",
            expected[(expected.IndexOf('\n') + 1)..],
            StringComparison.Ordinal);
    }

    [Fact]
    public void ChangedResidualBodyFailsByteVerification()
    {
        var candidate = EchoResidualBlock.Render(Summary);
        var expected = EchoResidualBlock.Render(
            Summary.Replace("unresolved_subitems: 1", "unresolved_subitems: 2", StringComparison.Ordinal));

        var error = EchoResidualBlock.Verify(
            Encoding.UTF8.GetBytes(candidate),
            Encoding.UTF8.GetBytes(expected));

        Assert.Equal("candidate block does not byte-match the derived residual summary", error);
    }

    [Fact]
    public void TamperedHeaderDigestFailsClosed()
    {
        var expected = EchoResidualBlock.Render(Summary);
        var digestIndex = expected.IndexOf("sha256:", StringComparison.Ordinal) + "sha256:".Length;
        var replacement = expected[digestIndex] == '0' ? '1' : '0';
        var candidate = expected[..digestIndex] + replacement + expected[(digestIndex + 1)..];

        var error = EchoResidualBlock.Verify(
            Encoding.UTF8.GetBytes(candidate),
            Encoding.UTF8.GetBytes(expected));

        Assert.Equal("candidate block does not byte-match the derived residual summary", error);
    }

    [Theory]
    [InlineData("review prose only\n", "candidate contains no echo residual summary block")]
    [InlineData("review prose only\n<!-- echo-residual-summary:v3 residual=sha256:05f4f3c3989efd7578fb7fdf6716b7a76aed13b8e840bd5a3fd624b86dd9bca9 -->\n", "candidate contains no echo residual summary block")]
    [InlineData("<!-- echo-residual-summary:v2 residual=sha256:05f4f3c3989efd7578fb7fdf6716b7a76aed13b8e840bd5a3fd624b86dd9bca9 -->\nbody\n", "candidate contains malformed echo residual summary marker")]
    [InlineData("<!-- echo-residual-summary:v3 residual=sha256:not-a-digest -->\nbody\n", "candidate contains malformed echo residual summary marker")]
    public void MissingOrMalformedMarkerFailsClosed(string candidate, string expectedError)
    {
        var expected = EchoResidualBlock.Render(Summary);

        var error = EchoResidualBlock.Verify(
            Encoding.UTF8.GetBytes(candidate),
            Encoding.UTF8.GetBytes(expected));

        Assert.Equal(expectedError, error);
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
