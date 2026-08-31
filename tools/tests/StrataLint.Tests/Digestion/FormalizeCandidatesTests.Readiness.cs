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
    public void ReadinessDistinguishesMissingFormalizationReceipt()
    {
        var entry = Entry(
            "source",
            "readiness-missing-receipt",
            "theorem",
            "16.21",
            atomizer: AtomizerRegistry.GenericId);

        var result = Run(
            [entry],
            atomizer: AtomizerRegistry.GenericId,
            arguments: ["--readiness"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var readiness = Assert.Single(json.RootElement.GetProperty("entries").EnumerateArray());
        Assert.Equal("deposit", readiness.GetProperty("action").GetString());
        Assert.Equal(
            ["formalization-receipt-missing"],
            readiness.GetProperty("ordered_blockers")
                .EnumerateArray()
                .Select(static item => item.GetString()));
    }

    [Fact]
    public void ReadinessDistinguishesExistingNonCurrentFormalizationReceipt()
    {
        var entry = Entry(
            "source",
            "readiness-stale-receipt",
            "theorem",
            "16.22",
            atomizer: AtomizerRegistry.GenericId);
        var staleReceipt = DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId,
            "D5/S0/Synthetic/Receipt.readiness_stale_receipt",
            new DigestionFormalizationSignature(
                "readiness_stale_receipt", "theorem", "statement-v1"),
            "sha256:" + new string('0', 64),
            entry.Atom.Fingerprints.RawSha256)).ToArray();

        var result = Run(
            [entry],
            formalizationReceipt: staleReceipt,
            atomizer: AtomizerRegistry.GenericId,
            arguments: ["--readiness"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var readiness = Assert.Single(json.RootElement.GetProperty("entries").EnumerateArray());
        Assert.Equal("deposit", readiness.GetProperty("action").GetString());
        Assert.Equal(
            ["formalization-receipt-stale"],
            readiness.GetProperty("ordered_blockers")
                .EnumerateArray()
                .Select(static item => item.GetString()));
    }

    [Fact]
    public void ReadinessFeedsCurrentReceiptAndScribeVerificationIntoClassifier()
    {
        var entry = Entry(
            "source",
            "readiness-current-receipt",
            "theorem",
            "16.23",
            atomizer: AtomizerRegistry.GenericId);

        var result = Run(
            [entry],
            formalizationReceipt: ValidReceipt(entry),
            scribeEmissions: ReadyScribe(entry),
            atomizer: AtomizerRegistry.GenericId,
            arguments: ["--readiness"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var readiness = Assert.Single(json.RootElement.GetProperty("entries").EnumerateArray());
        Assert.Equal("cover-now", readiness.GetProperty("action").GetString());
        Assert.Empty(readiness.GetProperty("ordered_blockers").EnumerateArray());
    }

    // 第三轮 quality 席实测:删掉 RenderReadiness 匿名对象里的 unknown_predicates 后,
    // 定向 81/81 全绿、零具名红,而真实 CLI 的 unknown_property_entries 从 15424 掉到 0 ——
    // 即那条「cover-now 不等于 make cover 一定成功」的诚实边界可以整个从输出消失而无人发现。
    // cover-now 必须携带 CoverAtomCommand 私有判据对应的 unknown 谓词,不得静默省略。
    [Fact]
    public void ReadinessCoverNowCarriesUnknownPredicatesInRenderedOutput()
    {
        var entry = Entry(
            "source",
            "readiness-unknown-predicates",
            "theorem",
            "16.31",
            atomizer: AtomizerRegistry.GenericId);

        var result = Run(
            [entry],
            formalizationReceipt: ValidReceipt(entry),
            scribeEmissions: ReadyScribe(entry),
            atomizer: AtomizerRegistry.GenericId,
            arguments: ["--readiness"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var readiness = Assert.Single(json.RootElement.GetProperty("entries").EnumerateArray());
        Assert.Equal("cover-now", readiness.GetProperty("action").GetString());
        var unknown = readiness.GetProperty("unknown_predicates")
            .EnumerateArray()
            .Select(static item => item.GetString())
            .ToArray();
        Assert.Contains("cover-atom:frozen-statement-resolution", unknown);
        Assert.Contains("cover-atom:baseline-precommitment-ownership", unknown);
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

    private static VerifiedScribeEmissions ReadyScribe(EntryFixture entry)
    {
        var gid = "D5/S0/Synthetic/Receipt." + entry.AtomId.Replace('-', '_');
        var documentGid = ScribeEmissionAttestation.DocumentGid(gid);
        return VerifiedScribeEmissions.Create(
            [
                new ScribeEmissionRecord(
                    documentGid,
                    ScribeEmissionAttestation.DefinitionPath(documentGid),
                    "sha256:" + new string('c', 64),
                    ScribeEmissionAttestation.EmissionPath(documentGid),
                    "sha256:" + new string('d', 64)),
            ],
            [gid]);
    }
}
