using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FormalizeCandidatesTests
{
    // Byte-faithful canonical status-marker forms used by theory atoms.
    private const string PlainClosedMarker = "〔closed〕";
    private const string QualifiedClosedMarker = "〔closed;数值证书〕";
    private const string UnterminatedPlainClosedMarker = "〔closed";
    private const string UnterminatedClosedMarker = "〔closed;数值证书";
    private const string WhitespaceOnlyClosedMarker = "〔closed;  〕";
    private const string WhitespaceBeforeSeparatorMarker = "〔closed ;数值证书〕";
    private const string FullwidthSeparatorMarker = "〔closed；数值证书〕";
    private const string WhitespaceStatusMarker = "〔 closed〕";
    private const string ExtraSeparatorMarker = "〔closed;数值证书;附注〕";
    private const string SpacedClosedMarker = "  〔closed〕";

    [Fact]
    public void StatusMarkerParserDoesNotScanLaterBodyBrackets()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 26.3**。正文随后提到〔closed〕。\n");

        var atom = Assert.Single(PzgAtomizer.Atomize(bytes).Claims);

        Assert.Equal(DigestionAtomStatusMarkerKind.Absent, atom.StatusMarker.Kind);
    }

    [Fact]
    public void FormalizeCandidatesIncludesOnlyAtomizerFormalizableKinds()
    {
        var entries = new[]
        {
            Entry("source", "theorem", "定理", "1.1"),
            Entry("source", "proposition", "命题", "1.2"),
            Entry("source", "lemma", "引理", "1.3"),
            Entry("source", "corollary", "推论", "1.4"),
            Entry("source", "observation", "观察", "1.5"),
            Entry("source", "remark", "评注", "1.6"),
            Entry("source", "definition", "定义", "1.7"),
            Entry("source", "theorem-form", "定理形", "1.8"),
        };

        var result = Run(entries);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            ["corollary", "lemma", "proposition", "theorem"],
            json.RootElement.GetProperty("candidates")
                .EnumerateArray()
                .Select(static candidate => candidate.GetProperty("kind").GetString())
                .Order(StringComparer.Ordinal));
    }

    [Fact]
    public void FormalizeCandidatesIncludesOnlyDerivedOpenEntriesWithEmptyCoverage()
    {
        var uncovered = Entry("source", "uncovered", "定理", "2.1");
        var covered = Entry(
            "source",
            "covered-closed",
            "定理",
            "2.2",
            coverageGids: ["D5/S0/Carrier/Nat"],
            migration: "absorbed",
            truth: "closed");

        var result = Run([covered, uncovered]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var candidate = Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray());
        Assert.Equal("uncovered", candidate.GetProperty("atom_id").GetString());
    }

    [Theory]
    [InlineData(false, "CAS blob is missing")]
    [InlineData(true, "CAS blob hash mismatch")]
    public void FormalizeCandidatesFailsClosedForMissingOrDriftedCas(
        bool includeDriftedBlob,
        string expectedError)
    {
        var entry = Entry("source", "candidate", "定理", "3.1");

        var result = Run(
            [entry],
            includeCas: includeDriftedBlob,
            driftCas: includeDriftedBlob);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Contains(expectedError, result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void FormalizeCandidatesUsesOrdinalSourceAndAtomOrdering()
    {
        var entries = new[]
        {
            Entry("source-2", "atom-q", "定理", "4.1"),
            Entry("source-10", "atom-z", "定理", "4.2"),
            Entry("source-10", "atom-a", "定理", "4.3"),
        };

        var result = Run(entries);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            ["source-10/atom-a", "source-10/atom-z", "source-2/atom-q"],
            json.RootElement.GetProperty("candidates")
                .EnumerateArray()
                .Select(static candidate =>
                    candidate.GetProperty("source_id").GetString()
                    + "/"
                    + candidate.GetProperty("atom_id").GetString()));
    }

    [Fact]
    public void FormalizeCandidatesReturnsAnEmptyArrayWhenNoCandidateExists()
    {
        var result = Run([Entry("source", "definition", "定义", "5.1")]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal("stratalint-formalize-candidates-v2", json.RootElement.GetProperty("schema").GetString());
        Assert.Empty(json.RootElement.GetProperty("candidates").EnumerateArray());
        Assert.Empty(json.RootElement.GetProperty("withheld").EnumerateArray());
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void FormalizeCandidatesKeepsAtomWhenReceiptContentDoesNotMatchCurrentEntry(
        bool mismatchCasRef)
    {
        var entry = Entry("source", "stale-receipt", "定理", "5.2");
        var receipt = DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId,
            "D5/S0/Synthetic/Receipt.stale_receipt",
            new DigestionFormalizationSignature("stale-receipt", "theorem", "statement-v1"),
            mismatchCasRef
                ? "sha256:0000000000000000000000000000000000000000000000000000000000000000"
                : entry.Atom.Fingerprints.RawSha256,
            mismatchCasRef
                ? entry.Atom.Fingerprints.RawSha256
                : "sha256:1111111111111111111111111111111111111111111111111111111111111111"))
            .ToArray();

        var result = Run([entry], formalizationReceipt: receipt);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            entry.AtomId,
            Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray())
                .GetProperty("atom_id")
                .GetString());
    }

    [Fact]
    public void FormalizeCandidatesKeepsAtomWhenReceiptDeclarationIsMissingFromCurrentLeanReport()
    {
        var entry = Entry("source", "missing-declaration", "定理", "5.3");

        var result = Run(
            [entry],
            formalizationReceipt: ValidReceipt(entry),
            leanReport: LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()));

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            entry.AtomId,
            Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray())
                .GetProperty("atom_id")
                .GetString());
    }

    [Fact]
    public void FormalizeCandidatesExcludesAtomCoveredByCurrentResolvableFormalizationReceipt()
    {
        var entry = Entry("source", "receipt-covered", "定理", "5.4");

        var result = Run([entry], formalizationReceipt: ValidReceipt(entry));

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Empty(json.RootElement.GetProperty("candidates").EnumerateArray());
        Assert.Empty(json.RootElement.GetProperty("withheld").EnumerateArray());
    }

    [Fact]
    public void FormalizeCandidatesKeepsAtomWhenReceiptSignatureDoesNotMatchCurrentDeclaration()
    {
        var entry = Entry("source", "signature-drift", "定理", "5.5");
        var receipt = DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId,
            "D5/S0/Synthetic/Receipt.signature_drift",
            new DigestionFormalizationSignature("different", "axiom", "False"),
            entry.Atom.Fingerprints.RawSha256,
            entry.Atom.Fingerprints.RawSha256)).ToArray();

        var result = Run([entry], formalizationReceipt: receipt);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            entry.AtomId,
            Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray())
                .GetProperty("atom_id")
                .GetString());
    }

    [Fact]
    public void FormalizationReconciliationKeepsNlOnlyReceiptLinksSemanticOpen()
    {
        var receiptLinked = Entry("source-2", "receipt-backed", "定理", "5.5");
        var semanticOpen = Entry("source-1", "nl-only", "定理", "5.6");

        var result = Run(
            [receiptLinked, semanticOpen],
            formalizationReceipts: new Dictionary<string, byte[]>(StringComparer.Ordinal)
            {
                [receiptLinked.AtomId] = CoverReadyReceipt(receiptLinked),
            },
            arguments: ["--formalization-reconciliation"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            "stratalint-formalization-reconciliation-v1",
            json.RootElement.GetProperty("schema").GetString());
        Assert.Equal(2, json.RootElement.GetProperty("residuals_total").GetInt32());
        Assert.Equal(1, json.RootElement.GetProperty("validated_receipt_total").GetInt32());
        Assert.Equal(0, json.RootElement.GetProperty("backfill_ready_total").GetInt32());
        Assert.Equal(2, json.RootElement.GetProperty("semantic_open_total").GetInt32());
        Assert.Empty(json.RootElement.GetProperty("backfill_ready").EnumerateArray());

        var open = json.RootElement.GetProperty("semantic_open")
            .EnumerateArray()
            .ToDictionary(
                static item => item.GetProperty("atom_id").GetString()!,
                StringComparer.Ordinal);
        var unlinked = open[semanticOpen.AtomId];
        Assert.Equal("source-1", unlinked.GetProperty("source_id").GetString());
        Assert.Equal("semantic-open", unlinked.GetProperty("status").GetString());
        Assert.Equal("none", unlinked.GetProperty("authority").GetString());
        Assert.Equal("none", unlinked.GetProperty("admission_effect").GetString());
        Assert.Equal("no-formalization-receipt", unlinked.GetProperty("reason").GetString());
        Assert.Equal(JsonValueKind.Null, unlinked.GetProperty("primary_gid").ValueKind);
        Assert.Equal(JsonValueKind.Null, unlinked.GetProperty("envelope_path").ValueKind);

        var linked = open[receiptLinked.AtomId];
        Assert.Equal("source-2", linked.GetProperty("source_id").GetString());
        Assert.Equal("semantic-open", linked.GetProperty("status").GetString());
        Assert.Equal("none", linked.GetProperty("authority").GetString());
        Assert.Equal("none", linked.GetProperty("admission_effect").GetString());
        Assert.Equal("nl-only-formalization-receipt", linked.GetProperty("reason").GetString());
        Assert.Equal(
            "D5/S0/Synthetic/Receipt.receipt_backed",
            linked.GetProperty("primary_gid").GetString());
        Assert.Equal(
            DigestionFormalizationReceipt.RootPath
                + receiptLinked.AtomId
                + DigestionFormalizationReceipt.PathSuffix,
            linked.GetProperty("envelope_path").GetString());
    }

    [Fact]
    public void FormalizationReconciliationFailsClosedForInvalidReceiptEvidence()
    {
        var entry = Entry("source", "invalid-receipt", "定理", "5.7");

        var result = Run(
            [entry],
            formalizationReceipt: Encoding.UTF8.GetBytes("{}\n"),
            arguments: ["--formalization-reconciliation"]);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Contains(
            "formalization receipt for atom invalid-receipt is invalid",
            result.Error,
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("{not-json}\n")]
    [InlineData("{}\n")]
    public void FormalizeCandidatesKeepsAtomWhenFormalizationReceiptIsMalformed(string receipt)
    {
        var entry = Entry("source", "malformed-receipt", "定理", "5.3");

        var result = Run([entry], formalizationReceipt: Encoding.UTF8.GetBytes(receipt));

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            entry.AtomId,
            Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray())
                .GetProperty("atom_id")
                .GetString());
        Assert.Empty(json.RootElement.GetProperty("withheld").EnumerateArray());
    }

    [Fact]
    public void FormalizeCandidatesKeepsAtomWhenReceiptAtomIdDoesNotMatchPath()
    {
        var entry = Entry("source", "receipt-path-owner", "定理", "5.4");
        var receipt = DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            "different-atom",
            "D5/S0/Synthetic/Receipt.different_atom",
            new DigestionFormalizationSignature("different-atom", "theorem", "statement-v1"),
            entry.Atom.Fingerprints.RawSha256,
            entry.Atom.Fingerprints.RawSha256)).ToArray();

        var result = Run([entry], formalizationReceipt: receipt);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            entry.AtomId,
            Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray())
                .GetProperty("atom_id")
                .GetString());
    }

    [Fact]
    public void FormalizeCandidatesKeepsAtomWhenMatchingReceiptPathIsNoncanonical()
    {
        var entry = Entry("source", "Uppercase-atom", "定理", "5.5");
        var receipt = DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId,
            "D5/S0/Synthetic/Receipt.Uppercase_atom",
            new DigestionFormalizationSignature("Uppercase_atom", "theorem", "statement-v1"),
            entry.Atom.Fingerprints.RawSha256,
            entry.Atom.Fingerprints.RawSha256)).ToArray();

        var result = Run([entry], formalizationReceipt: receipt);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            entry.AtomId,
            Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray())
                .GetProperty("atom_id")
                .GetString());
    }

    [Fact]
    public void FormalizeCandidatesReadsCompleteAtomTextFromCasAndAddressesLedgerBytes()
    {
        var entry = Entry(
            "source",
            "complete-atom",
            "定理",
            "6.1",
            body: "理论陈述。\n\n*证明*。完整推导。证毕。");
        var ledger = Ledger([entry]);

        var result = Run([entry], ledger: ledger);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(ledger)).RawSha256,
            json.RootElement.GetProperty("ledger_sha256").GetString());
        var candidate = Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray());
        Assert.Equal(
            Encoding.UTF8.GetString(entry.Atom.RawBytes.AsSpan()),
            candidate.GetProperty("atom_text").GetString());
        Assert.Contains("完整推导", candidate.GetProperty("atom_text").GetString(), StringComparison.Ordinal);
        Assert.Equal(entry.Atom.Fingerprints.RawSha256, candidate.GetProperty("raw_sha256").GetString());
        Assert.Equal(entry.Atom.Fingerprints.RawSha256, candidate.GetProperty("cas_ref").GetString());
    }

    [Fact]
    public void FormalizeCandidatesWithholdsQualifiedClosedStatusWithoutRejectingClosedPins()
    {
        var qualified = Entry(
            "source",
            "qualified-closed",
            "定理",
            "7.1",
            status: QualifiedClosedMarker);
        var plain = Entry(
            "source",
            "plain-closed",
            "定理",
            "7.2",
            status: PlainClosedMarker);
        var proved = Entry(
            "source",
            "proved-closed",
            "定理",
            "7.3",
            body: "陈述。\n\n*证明*。完整推导。证毕。",
            status: PlainClosedMarker);

        var result = Run([qualified, plain, proved]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal("stratalint-formalize-candidates-v2", json.RootElement.GetProperty("schema").GetString());
        Assert.Equal(
            ["plain-closed", "proved-closed"],
            json.RootElement.GetProperty("candidates")
                .EnumerateArray()
                .Select(static candidate => candidate.GetProperty("atom_id").GetString())
                .Order(StringComparer.Ordinal));
        var withheld = Assert.Single(json.RootElement.GetProperty("withheld").EnumerateArray());
        Assert.Equal("qualified-closed", withheld.GetProperty("atom_id").GetString());
        Assert.Equal("qualified-closed-status", withheld.GetProperty("withhold_reason").GetString());
        Assert.Equal("数值证书", withheld.GetProperty("status_qualifier").GetString());
    }

    [Theory]
    [InlineData("unterminated-plain-closed", UnterminatedPlainClosedMarker, null)]
    [InlineData("unterminated-closed", UnterminatedClosedMarker, "数值证书")]
    [InlineData("whitespace-only-closed", WhitespaceOnlyClosedMarker, "  ")]
    [InlineData("whitespace-before-separator", WhitespaceBeforeSeparatorMarker, "数值证书")]
    [InlineData("fullwidth-separator", FullwidthSeparatorMarker, null)]
    [InlineData("whitespace-status", WhitespaceStatusMarker, null)]
    [InlineData("extra-separator", ExtraSeparatorMarker, "数值证书;附注")]
    [InlineData("spaced-closed", SpacedClosedMarker, null)]
    public void FormalizeCandidatesWithholdsMalformedClosedStatusMarkers(
        string atomId,
        string marker,
        string? expectedQualifier)
    {
        var malformed = Entry("source", atomId, "定理", "7.4", status: marker);

        var result = Run([malformed]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Empty(json.RootElement.GetProperty("candidates").EnumerateArray());
        var withheld = Assert.Single(json.RootElement.GetProperty("withheld").EnumerateArray());
        Assert.Equal(atomId, withheld.GetProperty("atom_id").GetString());
        Assert.Equal("malformed-status-marker", withheld.GetProperty("withhold_reason").GetString());
        var qualifier = withheld.GetProperty("status_qualifier");
        if (expectedQualifier is null)
        {
            Assert.Equal(JsonValueKind.Null, qualifier.ValueKind);
        }
        else
        {
            Assert.Equal(expectedQualifier, qualifier.GetString());
        }
    }

    private static CommandResult Run(
        IReadOnlyList<EntryFixture> entries,
        bool includeCas = true,
        bool driftCas = false,
        string? ledger = null,
        byte[]? formalizationReceipt = null,
        LeanAxiomReport? leanReport = null,
        IReadOnlyDictionary<string, byte[]>? formalizationReceipts = null,
        IReadOnlyList<string>? arguments = null)
    {
        var sources = entries
            .GroupBy(static entry => entry.SourceId, StringComparer.Ordinal)
            .Select(group =>
            {
                var bytes = ImmutableArray.CreateRange(
                    group.SelectMany(static entry => entry.Atom.RawBytes));
                var atoms = PzgAtomizer.Atomize(bytes.AsSpan()).Claims;
                var fixtures = group.ToArray();
                Assert.Equal(fixtures.Length, atoms.Length);
                return new SourceFixture(
                    group.Key,
                    bytes,
                    fixtures.Select((entry, index) => entry with { Atom = atoms[index] }).ToArray());
            })
            .ToArray();
        entries = sources.SelectMany(static source => source.Entries).ToArray();
        ledger ??= Ledger(entries);
        var files = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText(BackfillInventoryLoader.RelativePath, ledger),
        };
        foreach (var source in sources)
        {
            files.Add(new RawRepositoryEntry(
                $"synthetic/{source.SourceId}.md",
                source.RawBytes));
        }
        if (includeCas)
        {
            foreach (var entry in entries)
            {
                var captured = DigestionCasStore.Capture(entry.Atom.RawBytes.AsSpan());
                var bytes = driftCas
                    ? ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("drifted CAS bytes\n"))
                    : captured.Bytes;
                files.Add(new RawRepositoryEntry(captured.RelativePath, bytes));
            }
        }

        if (formalizationReceipt is not null)
        {
            Assert.Single(entries);
            files.Add(new RawRepositoryEntry(
                DigestionFormalizationReceipt.RootPath
                    + entries[0].AtomId
                    + DigestionFormalizationReceipt.PathSuffix,
                ImmutableArray.CreateRange(formalizationReceipt)));
        }

        if (formalizationReceipts is not null)
        {
            foreach (var (atomId, receipt) in formalizationReceipts)
            {
                files.Add(new RawRepositoryEntry(
                    DigestionFormalizationReceipt.RootPath
                        + atomId
                        + DigestionFormalizationReceipt.PathSuffix,
                    ImmutableArray.CreateRange(receipt)));
            }
        }

        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                RawRepositorySnapshot.Create(files),
                null),
            new FakeLeanReportSource(leanReport ?? CurrentLeanReport(entries)),
            new FakeScribeEmissionVerifier(null));
        return environment.DigestStatus(arguments ?? ["--formalize-candidates"]);
    }

    private static byte[] ValidReceipt(EntryFixture entry) =>
        CoverReadyReceipt(entry);

    private static byte[] CoverReadyReceipt(EntryFixture entry)
    {
        var selector = entry.AtomId.Replace('-', '_');
        return DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId,
            "D5/S0/Synthetic/Receipt." + selector,
            new DigestionFormalizationSignature(selector, "theorem", "statement-v1"),
            entry.Atom.Fingerprints.RawSha256,
            entry.Atom.Fingerprints.RawSha256)).ToArray();
    }

    private static LeanAxiomReport CurrentLeanReport(IReadOnlyList<EntryFixture> entries) =>
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            ["D5/S0/Synthetic/Receipt.lean"] = new LeanFileReport(
                ImmutableArray<string>.Empty,
                entries.Select(static entry => new LeanDeclaration(
                    entry.AtomId.Replace('-', '_'),
                    "theorem",
                    "statement-v1",
                    ImmutableArray<string>.Empty)).ToImmutableArray()),
        });

    private static EntryFixture Entry(
        string sourceId,
        string atomId,
        string kind,
        string number,
        string body = "陈述。",
        string[]? coverageGids = null,
        string migration = "residual",
        string truth = "open",
        string status = "")
    {
        var source = Encoding.UTF8.GetBytes(
            status is UnterminatedPlainClosedMarker or UnterminatedClosedMarker
            ? $"# Synthetic\n\n**{kind} {number}**{status}"
            : $"# Synthetic\n\n**{kind} {number}**{status}。{body}\n");
        var atom = Assert.Single(PzgAtomizer.Atomize(source).Claims);
        return new EntryFixture(
            sourceId,
            atomId,
            atom,
            coverageGids ?? [],
            migration,
            truth);
    }

    private static string Ledger(IReadOnlyList<EntryFixture> entries)
    {
        var builder = new StringBuilder();
        builder.AppendLine("schema_version: 3");
        builder.AppendLine("ledger: theory-digestion-v1");
        builder.AppendLine("sources:");
        foreach (var source in entries.GroupBy(static entry => entry.SourceId, StringComparer.Ordinal))
        {
            builder.AppendLine($"  - source_id: {source.Key}");
            builder.AppendLine($"    path: synthetic/{source.Key}.md");
            builder.AppendLine($"    atomizer: {AtomizerRegistry.PzgId}");
            builder.AppendLine("    acknowledged_stale: []");
            builder.AppendLine("    entries:");
            foreach (var entry in source)
            {
                builder.AppendLine($"      - atom_id: {entry.AtomId}");
                builder.AppendLine($"        ast_path: {entry.Atom.AstPath}");
                builder.AppendLine("        fingerprints:");
                builder.AppendLine($"          raw_sha256: {entry.Atom.Fingerprints.RawSha256}");
                builder.AppendLine($"          normalized_sha256: {entry.Atom.Fingerprints.NormalizedSha256}");
                builder.AppendLine($"        cas_ref: {entry.Atom.Fingerprints.RawSha256}");
                if (entry.CoverageGids.Length == 0)
                {
                    builder.AppendLine("        coverage_gids: []");
                }
                else
                {
                    builder.AppendLine("        coverage_gids:");
                    foreach (var gid in entry.CoverageGids)
                    {
                        builder.AppendLine($"          - {gid}");
                    }
                }

                builder.AppendLine("        receipts:");
                builder.AppendLine("          coverage: []");
                builder.AppendLine("          scribe: []");
                builder.AppendLine("          unresolved_subitems: []");
                builder.AppendLine("          chain_atoms: []");
                builder.AppendLine("          tail_authorization: null");
                builder.AppendLine("        status:");
                builder.AppendLine($"          migration: {entry.Migration}");
                builder.AppendLine($"          truth: {entry.Truth}");
            }
        }

        builder.AppendLine("ticket_index: []");
        return builder.ToString();
    }

    private sealed record EntryFixture(
        string SourceId,
        string AtomId,
        DigestionAtom Atom,
        string[] CoverageGids,
        string Migration,
        string Truth);

    private sealed record SourceFixture(
        string SourceId,
        ImmutableArray<byte> RawBytes,
        EntryFixture[] Entries);
}
