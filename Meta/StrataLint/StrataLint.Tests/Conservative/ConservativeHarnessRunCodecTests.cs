using StrataLint.Cli;
using System.Text;
using System.Collections.Immutable;

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

    [Fact]
    public void ForgedSl022DiagnosticTupleFailsClosed()
    {
        var input = Assert.IsType<ConservativeHarnessExecution.Completed>(
            ConservativeTestData.Input().BaselineExecution).Run;
        var canonical = ConservativeHarnessRunCodec.Write(input);
        var text = Encoding.UTF8.GetString(canonical.AsSpan()).Replace(
            "\"rule_id\": \"SL-022\"",
            "\"rule_id\": \"SL-001\"",
            StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() =>
            ConservativeHarnessRunCodec.Read(Encoding.UTF8.GetBytes(text)));

        Assert.Contains("SL-022", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GoldenAdmitCannotCarryBlockingRules()
    {
        var input = Assert.IsType<ConservativeHarnessExecution.Completed>(
            ConservativeTestData.Input().BaselineExecution).Run;
        var contradictory = input with
        {
            Cases = input.Cases.Select(item => ConservativeTestData.WithDisposition(
                    item,
                    ConservativeTestData.RejectCase,
                    ConservativeDisposition.Admit,
                    "SL-001"))
                .ToImmutableArray(),
        };
        var canonical = ConservativeHarnessRunCodec.Write(contradictory);

        var exception = Assert.Throws<FormatException>(() =>
            ConservativeHarnessRunCodec.Read(canonical.AsSpan()));

        Assert.Contains("blocking", exception.Message, StringComparison.OrdinalIgnoreCase);
    }
}
