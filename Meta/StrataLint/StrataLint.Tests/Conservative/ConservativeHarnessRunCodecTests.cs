using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ConservativeHarnessRunCodecTests
{
    [Fact]
    public void HarnessResultRoundTripsAsCanonicalBytes()
    {
        var input = Assert.IsType<ConservativeHarnessExecution.Completed>(
            ConservativeTestData.Input().BaselineExecution).Run;

        var first = ConservativeHarnessRunCodec.Write(input);
        var decoded = ConservativeHarnessRunCodec.Read(first.AsSpan());
        var second = ConservativeHarnessRunCodec.Write(decoded);

        Assert.Equal(input.HarnessRoot, decoded.HarnessRoot);
        Assert.Equal(input.ActiveRules.ToArray(), decoded.ActiveRules.ToArray());
        Assert.Equal(
            input.Cases.Select(static item => item.CaseId).Order(StringComparer.Ordinal),
            decoded.Cases.Select(static item => item.CaseId));
        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
    }

    [Fact]
    public void NoncanonicalHarnessResultFailsClosed()
    {
        var input = Assert.IsType<ConservativeHarnessExecution.Completed>(
            ConservativeTestData.Input().BaselineExecution).Run;
        var canonical = ConservativeHarnessRunCodec.Write(input);
        var padded = canonical.Insert(0, (byte)' ');

        var exception = Assert.Throws<FormatException>(() =>
            ConservativeHarnessRunCodec.Read(padded.AsSpan()));

        Assert.Contains("canonical", exception.Message, StringComparison.OrdinalIgnoreCase);
    }
}
