using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class FormalizeCandidatesTests
{
    [Fact]
    public void ReadinessOptionDispatchesToReadinessJsonRenderer()
    {
        var entry = Entry(
            "source",
            "readiness-dispatch",
            "theorem",
            "16.20",
            atomizer: AtomizerRegistry.GenericId);

        var result = Run(
            [entry],
            atomizer: AtomizerRegistry.GenericId,
            arguments: ["--readiness"]);

        Assert.True(result.Success, result.Error);
        Assert.False(result.Output.StartsWith("DIGEST_STATUS ", StringComparison.Ordinal));
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            "stratalint-digestion-readiness-v1",
            json.RootElement.GetProperty("schema").GetString());
        var readiness = Assert.Single(json.RootElement.GetProperty("entries").EnumerateArray());
        Assert.Equal(entry.AtomId, readiness.GetProperty("atom_id").GetString());
        Assert.False(readiness.TryGetProperty("ast_path", out _));
    }


    [Fact]
    public void ReadinessFeedsAcknowledgedStaleLedgerIntoClassifier()
    {
        var entry = Entry(
            "source",
            "readiness-acknowledged-stale",
            "theorem",
            "16.24",
            atomizer: AtomizerRegistry.GenericId);
        var ledger = Ledger([entry], AtomizerRegistry.GenericId);
        var staleLedger = ledger.WithDigestionSources(
        [
            Assert.Single(ledger.RequireDigestionSources()) with
            {
                AcknowledgedStale = [entry.AtomId],
            },
        ]);

        var result = Run(
            [entry],
            ledger: staleLedger,
            atomizer: AtomizerRegistry.GenericId,
            arguments: ["--readiness"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var readiness = Assert.Single(json.RootElement.GetProperty("entries").EnumerateArray());
        Assert.Equal("refresh-stale", readiness.GetProperty("action").GetString());
        Assert.Equal(
            ["acknowledged-stale"],
            readiness.GetProperty("ordered_blockers")
                .EnumerateArray()
                .Select(static item => item.GetString()));
    }

    [Theory]
    [InlineData("theorem", "16.25", true)]
    [InlineData("section", "16.26", false)]
    public void FormalizeCandidatesAndReadinessUseTheSameFormalizableKindDecision(
        string kind,
        string number,
        bool expectedFormalizable)
    {
        var entry = Entry(
            "source",
            "shared-kind-" + number.Replace('.', '-'),
            kind,
            number,
            atomizer: AtomizerRegistry.GenericId);

        var formalizeResult = Run(
            [entry],
            atomizer: AtomizerRegistry.GenericId,
            arguments: ["--formalize-candidates"]);
        var readinessResult = Run(
            [entry],
            atomizer: AtomizerRegistry.GenericId,
            arguments: ["--readiness"]);

        Assert.True(formalizeResult.Success, formalizeResult.Error);
        Assert.True(readinessResult.Success, readinessResult.Error);
        using var formalizeJson = JsonDocument.Parse(formalizeResult.Output);
        using var readinessJson = JsonDocument.Parse(readinessResult.Output);
        var candidateExists = formalizeJson.RootElement.GetProperty("candidates").GetArrayLength() == 1;
        var readinessAction = Assert.Single(
                readinessJson.RootElement.GetProperty("entries").EnumerateArray())
            .GetProperty("action")
            .GetString();
        var readinessTreatsKindAsFormalizable = readinessAction is not (
            "needs-routing" or "not-formalizable");

        Assert.Equal(expectedFormalizable, candidateExists);
        Assert.Equal(expectedFormalizable, readinessTreatsKindAsFormalizable);
    }

}
