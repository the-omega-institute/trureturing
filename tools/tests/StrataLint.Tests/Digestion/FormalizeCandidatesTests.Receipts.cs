using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class FormalizeCandidatesTests
{
    [Fact]
    public void FormalizeCandidatesWithholdsRecordedCoverDisposition()
    {
        var entry = Entry(
            "pzg-v170",
            "c2b458c0ec6e7494ffe7b15cc71ca9aa7afd5559254301851904c9c91c88d13f",
            "定理",
            "19.5",
            coverDisposition: new DigestionCoverDisposition(
                new DigestionStatus(
                    DigestionMigrationState.Partial,
                    DigestionTruthState.Closed),
                ["D5/S0/Synthetic/Receipt.pzg_residual"],
                [new DigestionDispositionGap("unresolved-subitem", "remaining theorem clause")],
                new DateTimeOffset(2026, 8, 25, 4, 3, 2, TestBudgets.ZeroDuration)));

        var result = Run([entry], formalizationReceipt: ValidReceipt(entry));

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Empty(json.RootElement.GetProperty("candidates").EnumerateArray());
        Assert.Empty(json.RootElement.GetProperty("recorded_formalizations").EnumerateArray());
        var withheld = Assert.Single(json.RootElement.GetProperty("withheld").EnumerateArray());
        Assert.Equal(entry.AtomId, withheld.GetProperty("atom_id").GetString());
        Assert.Equal("cover-disposition", withheld.GetProperty("withhold_reason").GetString());
    }

    [Fact]
    public void FormalizeCandidatesRetryDispositionRedispatchesAtom()
    {
        var entry = Entry(
            "pzg-v170",
            "c2b458c0ec6e7494ffe7b15cc71ca9aa7afd5559254301851904c9c91c88d13f",
            "定理",
            "19.5",
            coverDisposition: new DigestionCoverDisposition(
                new DigestionStatus(
                    DigestionMigrationState.Partial,
                    DigestionTruthState.Closed),
                ["D5/S0/Synthetic/Receipt.pzg_residual"],
                [new DigestionDispositionGap("unresolved-subitem", "remaining theorem clause")],
                new DateTimeOffset(2026, 8, 25, 4, 3, 2, TestBudgets.ZeroDuration)));

        var result = Run(
            [entry],
            formalizationReceipt: ValidReceipt(entry),
            arguments: ["--formalize-candidates", "--retry-dispositions"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var candidate = Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray());
        Assert.Equal(entry.AtomId, candidate.GetProperty("atom_id").GetString());
        Assert.Empty(json.RootElement.GetProperty("recorded_formalizations").EnumerateArray());
        Assert.Empty(json.RootElement.GetProperty("withheld").EnumerateArray());
    }

    [Fact]
    public void CoverDispositionDoesNotChangeAdmissionProjection()
    {
        const string atomId =
            "c2b458c0ec6e7494ffe7b15cc71ca9aa7afd5559254301851904c9c91c88d13f";
        var plain = Entry("pzg-v170", atomId, "定理", "19.5");
        var dispositioned = Entry(
            "pzg-v170",
            atomId,
            "定理",
            "19.5",
            coverDisposition: new DigestionCoverDisposition(
                new DigestionStatus(
                    DigestionMigrationState.Partial,
                    DigestionTruthState.Closed),
                ["D5/S0/Synthetic/Receipt.pzg_residual"],
                [new DigestionDispositionGap("unresolved-subitem", "remaining theorem clause")],
                new DateTimeOffset(2026, 8, 25, 4, 3, 2, TestBudgets.ZeroDuration)));

        var before = Run([plain], arguments: ["--json"]);
        var after = Run([dispositioned], arguments: ["--json"]);

        Assert.True(before.Success, before.Error);
        Assert.True(after.Success, after.Error);
        Assert.Equal(before.Output, after.Output);
    }

    [Fact]
    public void RetryDispositionsRequiresFormalizeCandidates()
    {
        var result = Run(
            [Entry("pzg-v170", new string('c', 64), "定理", "19.5")],
            arguments: ["--retry-dispositions"]);

        Assert.False(result.Success);
        Assert.Contains("USAGE", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void FormalizeCandidatesReportsRecordedFormalizationWithEmptyCoverageSeparately()
    {
        var entry = Entry(
            "pzg-v170",
            "c2b458c0ec6e7494ffe7b15cc71ca9aa7afd5559254301851904c9c91c88d13f",
            "定理",
            "19.5");
        var primaryGid = "D5/S0/Synthetic/Receipt." + entry.AtomId.Replace('-', '_');
        const string firstHostedGid = "D5/S0/Synthetic/Receipt.hosted_a";
        const string secondHostedGid = "D5/S0/Synthetic/Receipt.hosted_z";
        var receipt = DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId,
            primaryGid,
            new DigestionFormalizationSignature(
                entry.AtomId.Replace('-', '_'), "theorem", "statement-v1"),
            entry.Atom.Fingerprints.RawSha256,
            entry.Atom.Fingerprints.RawSha256,
            [
                new DigestionFormalizationExtension(
                    firstHostedGid,
                    new DigestionFormalizationSignature("hosted_a", "theorem", "statement-a")),
                new DigestionFormalizationExtension(
                    secondHostedGid,
                    new DigestionFormalizationSignature("hosted_z", "theorem", "statement-z")),
            ])).ToArray();
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/S0/Synthetic/Receipt.lean"] = new LeanFileReport(
                [],
                [
                    new LeanDeclaration(
                        entry.AtomId.Replace('-', '_'), "theorem", "statement-v1", []),
                    new LeanDeclaration("hosted_a", "theorem", "statement-a", []),
                    new LeanDeclaration("hosted_z", "theorem", "statement-z", []),
                ]),
        });

        var result = Run([entry], formalizationReceipt: receipt, leanReport: report);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal("stratalint-formalize-candidates-v4", json.RootElement.GetProperty("schema").GetString());
        Assert.Empty(json.RootElement.GetProperty("candidates").EnumerateArray());
        Assert.Empty(json.RootElement.GetProperty("withheld").EnumerateArray());
        var recorded = Assert.Single(
            json.RootElement.GetProperty("recorded_formalizations").EnumerateArray());
        Assert.Equal("pzg-v170", recorded.GetProperty("source_id").GetString());
        Assert.Equal(entry.AtomId, recorded.GetProperty("atom_id").GetString());
        Assert.Equal(
            "current-formalization-receipt",
            recorded.GetProperty("evidence_kind").GetString());
        Assert.Equal(primaryGid, recorded.GetProperty("primary_gid").GetString());
        Assert.Equal(
            [primaryGid, firstHostedGid, secondHostedGid],
            recorded.GetProperty("gids").EnumerateArray().Select(static gid => gid.GetString()));
        Assert.Equal(
            DigestionFormalizationReceipt.RootPath
                + entry.AtomId
                + DigestionFormalizationReceipt.PathSuffix,
            recorded.GetProperty("receipt_path").GetString());
    }

    [Fact]
    public void FormalizeCandidatesExplicitlySelectsACoveredAtomForSecondaryFormalization()
    {
        const string gid = "D5/S0/Carrier/Probe.probe";
        var spec = new CoverSpec
        {
            InitialCoverage = [gid],
            InitialDefinitionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256,
            InitialEmissionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256,
            Migration = "absorbed",
            Truth = "closed",
        };
        var inputs = spec.Materialize();

        var result = CoverWorld.Environment("/repo", inputs, inputs.Files).DigestStatus(
            ["--formalize-candidates", "--atom-id", spec.AtomId]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Empty(json.RootElement.GetProperty("candidates").EnumerateArray());
        var recorded = Assert.Single(
            json.RootElement.GetProperty("recorded_formalizations").EnumerateArray());
        Assert.Equal(spec.AtomId, recorded.GetProperty("atom_id").GetString());
        Assert.Equal(
            [gid],
            recorded.GetProperty("gids").EnumerateArray().Select(static gid => gid.GetString()));
    }

    [Fact]
    public void ExplicitFormalizeCandidateRejectsReceiptIntegrityFailure()
    {
        var spec = CoverWorld.StaleReceiptSpec();
        var inputs = spec.Materialize();

        var result = CoverWorld.Environment("/repo", inputs, inputs.Files).DigestStatus(
            ["--formalize-candidates", "--atom-id", spec.AtomId]);

        Assert.False(result.Success);
        Assert.Contains("scribe-definition-mismatch", result.Error, StringComparison.Ordinal);
    }
}
