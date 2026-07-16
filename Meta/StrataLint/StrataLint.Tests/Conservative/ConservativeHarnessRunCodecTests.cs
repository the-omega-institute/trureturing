using StrataLint.Cli;
using System.Text;
using System.Collections.Immutable;
using System.Text.Json;

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
        Assert.Equal(input.Policy.Root, decoded.Policy.Root);
        Assert.Equal(input.Policy.CanonicalBytes.ToArray(), decoded.Policy.CanonicalBytes.ToArray());
        Assert.Equal(
            input.Cases.Select(static item => item.CaseId).Order(StringComparer.Ordinal),
            decoded.Cases.Select(static item => item.CaseId));
        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
    }

    [Fact]
    public void PolicyUsesTheExistingV1ActiveRulesCarrier()
    {
        var input = Assert.IsType<ConservativeHarnessExecution.Completed>(
            ConservativeTestData.Input().BaselineExecution).Run;

        var bytes = ConservativeHarnessRunCodec.Write(input);
        using var document = JsonDocument.Parse(bytes.ToArray());
        var root = document.RootElement;
        var properties = root.EnumerateObject().Select(static item => item.Name).ToArray();
        var active = root.GetProperty("active_rules")
            .EnumerateArray()
            .Select(static item => item.GetString()!)
            .ToArray();

        Assert.Equal("stratalint-conservative-harness-result-v1", root.GetProperty("schema").GetString());
        Assert.Equal(["active_rules", "cases", "harness_root", "schema"], properties);
        Assert.Single(active, ConservativePolicySnapshot.IsMarker);
    }

    [Fact]
    public void MissingPolicyMarkerFailsClosedForTheNewBaseComparator()
    {
        var input = Assert.IsType<ConservativeHarnessExecution.Completed>(
            ConservativeTestData.Input().BaselineExecution).Run;
        var canonical = ConservativeHarnessRunCodec.Write(input);
        using var document = JsonDocument.Parse(canonical.ToArray());
        var material = JsonSerializer.SerializeToElement(new
        {
            active_rules = input.ActiveRules,
            cases = document.RootElement.GetProperty("cases"),
            harness_root = input.HarnessRoot,
            schema = "stratalint-conservative-harness-result-v1",
        });
        var withoutPolicy = StrataLint.Engine.StructuredCanonicalWriter.WriteJson(material);

        var exception = Assert.Throws<FormatException>(() =>
            ConservativeHarnessRunCodec.Read(withoutPolicy.AsSpan()));

        Assert.Contains("policy marker", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ContractCorpusResultsRoundTripThroughTheV1Carrier()
    {
        var original = Assert.IsType<ConservativeHarnessExecution.Completed>(
            ConservativeTestData.Input().BaselineExecution).Run;
        var input = original with
        {
            ContractCases =
            [
                new ConservativeContractCaseResult(
                    "contract:negative",
                    ["CONTRACT-EPOCH-UNCOVERED-OBLIGATION"]),
            ],
        };

        var bytes = ConservativeHarnessRunCodec.Write(input);
        var decoded = ConservativeHarnessRunCodec.Read(bytes.AsSpan());
        using var document = JsonDocument.Parse(bytes.ToArray());
        var active = document.RootElement.GetProperty("active_rules")
            .EnumerateArray()
            .Select(static item => item.GetString()!)
            .ToArray();

        var result = Assert.Single(decoded.ContractCases);
        Assert.Equal("contract:negative", result.CaseId);
        Assert.Equal(
            ["CONTRACT-EPOCH-UNCOVERED-OBLIGATION"],
            result.FindingCodes.ToArray());
        Assert.Single(active, ContractEpochCorpusMarker.IsMarker);
        Assert.Equal(
            ["active_rules", "cases", "harness_root", "schema"],
            document.RootElement.EnumerateObject().Select(static item => item.Name).ToArray());
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
