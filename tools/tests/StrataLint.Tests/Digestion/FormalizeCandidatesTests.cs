using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class FormalizeCandidatesTests
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

        var atom = Assert.Single(PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);

        Assert.Equal(DigestionAtomStatusMarkerKind.Absent, atom.StatusMarker.Kind);
    }

    [Theory]
    [InlineData("〔定理·证 + 证书〕")]
    [InlineData("〔closed·数值(五仪终审)+ 解析证明待办;v3.7 改版〕")]
    public void FormalizeCandidatesIncludeAtomsWithNonStatusGictAnnotations(string annotation)
    {
        var entry = Entry("source", "gict-annotation", "定理", "7.12", status: annotation);

        var result = Run([entry]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            "gict-annotation",
            Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray())
                .GetProperty("atom_id")
                .GetString());
        Assert.Empty(json.RootElement.GetProperty("withheld").EnumerateArray());
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

    [Theory]
    [InlineData("定理", "16.8", true)]
    [InlineData("命题", "16.9", true)]
    [InlineData("引理", "16.10", true)]
    [InlineData("推论", "16.11", true)]
    [InlineData("theorem", "16.12", true)]
    [InlineData("proposition", "16.13", true)]
    [InlineData("lemma", "16.14", true)]
    [InlineData("corollary", "16.15", true)]
    [InlineData("section", "16.16", false)]
    [InlineData("定义", "16.17", false)]
    [InlineData("row", "16.18", false)]
    [InlineData("item", "16.19", false)]
    public void FormalizeCandidatesKindAlphabetIsClosed(
        string kind,
        string number,
        bool expectedCandidate)
    {
        var entry = Entry(
            "source",
            "kind-alphabet-" + number.Replace('.', '-'),
            kind,
            number,
            atomizer: AtomizerRegistry.GenericId);
        var result = Run([entry], atomizer: AtomizerRegistry.GenericId);

        Assert.Equal(
            DigestionFingerprint.Compute(entry.Atom.RawBytes.AsSpan()).RawSha256,
            entry.Atom.Fingerprints.RawSha256);
        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var candidates = json.RootElement.GetProperty("candidates").EnumerateArray().ToArray();
        if (expectedCandidate)
        {
            var candidate = Assert.Single(candidates);
            Assert.Equal(entry.AtomId, candidate.GetProperty("atom_id").GetString());
            Assert.Equal(kind, candidate.GetProperty("kind").GetString());
            Assert.False(candidate.TryGetProperty("ast_path", out _));
        }
        else
        {
            Assert.Empty(candidates);
        }
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

    [Fact]
    public void FormalizeCandidatesRejectsDuplicateAtomIds()
    {
        var first = Entry("source-a", "duplicate-atom", "定理", "2.3");
        var second = Entry("source-b", "duplicate-atom", "定理", "2.4");

        var result = Run([first, second]);

        Assert.False(result.Success);
        Assert.Contains("duplicate atom_id: duplicate-atom", result.Error, StringComparison.Ordinal);
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
        var result = Run(
        [
            Entry(
                "source",
                "complete",
                "定义",
                "5.1",
                coverageGids: ["D5/S0/Carrier/Nat"],
                migration: "absorbed",
                truth: "closed"),
        ]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal("stratalint-formalize-candidates-v4", json.RootElement.GetProperty("schema").GetString());
        Assert.Empty(json.RootElement.GetProperty("candidates").EnumerateArray());
        Assert.Empty(json.RootElement.GetProperty("recorded_formalizations").EnumerateArray());
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
    public void FormalizeCandidatesDoesNotTreatDriftedReceiptSignatureAsCurrentFormalization()
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
        Assert.Empty(json.RootElement.GetProperty("recorded_formalizations").EnumerateArray());
    }

    [Fact]
    public void FormalizeCandidatesDoesNotTreatDriftedHostedSignatureAsCurrentFormalization()
    {
        var entry = Entry("source", "hosted-signature-drift", "定理", "5.6");
        const string hostedGid = "D5/S0/Synthetic/Receipt.hosted_secondary";
        var receipt = DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId,
            "D5/S0/Synthetic/Receipt.hosted_signature_drift",
            new DigestionFormalizationSignature(
                "hosted_signature_drift", "theorem", "statement-v1"),
            entry.Atom.Fingerprints.RawSha256,
            entry.Atom.Fingerprints.RawSha256,
            [
                new DigestionFormalizationExtension(
                    hostedGid,
                    new DigestionFormalizationSignature(
                        "hosted_secondary", "theorem", "hosted-statement-v1")),
            ])).ToArray();
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/S0/Synthetic/Receipt.lean"] = new LeanFileReport(
                [],
                [
                    new LeanDeclaration(
                        "hosted_signature_drift", "theorem", "statement-v1", []),
                    new LeanDeclaration(
                        "hosted_secondary", "theorem", "hosted-statement-v2", []),
                ]),
        });

        var result = Run([entry], formalizationReceipt: receipt, leanReport: report);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            entry.AtomId,
            Assert.Single(json.RootElement.GetProperty("candidates").EnumerateArray())
                .GetProperty("atom_id")
                .GetString());
        Assert.Empty(json.RootElement.GetProperty("recorded_formalizations").EnumerateArray());
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
            DigestionLedgerPreimage.ComputeSha256(ledger),
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
    public void DirectoryLedgerHashChangesWhenOnlyGenreRegistryCheckChanges()
    {
        var ledger = Ledger([Entry("source", "complete-atom", "定理", "6.2")]);
        var source = Assert.Single(ledger.RequireDigestionSources());
        var changed = ledger.WithDigestionSources(
        [
            source with
            {
                GenreRegistryProjection = GenreRegistryProjection.Available(
                    GenreRegistryCheck.NoGenreRegistry),
            },
        ]);

        var before = DigestionLedgerPreimage.ComputeSha256(ledger);
        var after = DigestionLedgerPreimage.ComputeSha256(changed);

        Assert.NotEqual(before, after);
    }

    [Fact]
    public void DirectoryLedgerHashChangesWhenOnlyUnregisteredGenresChange()
    {
        var ledger = Ledger([Entry("source", "complete-atom", "定理", "6.3")]);
        var source = Assert.Single(ledger.RequireDigestionSources());
        var changed = ledger.WithDigestionSources(
        [
            source with
            {
                GenreRegistryProjection = GenreRegistryProjection.Available(
                    GenreRegistryCheck.Collected(["未登记体"])),
            },
        ]);

        var before = DigestionLedgerPreimage.ComputeSha256(ledger);
        var after = DigestionLedgerPreimage.ComputeSha256(changed);

        Assert.NotEqual(before, after);
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
        Assert.Equal("stratalint-formalize-candidates-v4", json.RootElement.GetProperty("schema").GetString());
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
        BackfillInventoryDocument? ledger = null,
        byte[]? formalizationReceipt = null,
        LeanAxiomReport? leanReport = null,
        VerifiedScribeEmissions? scribeEmissions = null,
        string atomizer = AtomizerRegistry.PzgId,
        IReadOnlyList<string>? arguments = null,
        byte[]? rulesBytes = null)
    {
        var sources = entries
            .GroupBy(static entry => entry.SourceId, StringComparer.Ordinal)
            .Select(group =>
            {
                var bytes = ImmutableArray.CreateRange(
                    group.SelectMany(static entry => entry.Atom.RawBytes));
                var rules = string.Equals(atomizer, AtomizerRegistry.GenericId, StringComparison.Ordinal)
                    ? TheoryAtomizerRules.None
                    : DigestionTestSupport.Rules;
                var atoms = AtomizerRegistry.Atomize(atomizer, bytes.AsSpan(), rules).Claims;
                var fixtures = group.ToArray();
                Assert.Equal(fixtures.Length, atoms.Length);
                return new SourceFixture(
                    group.Key,
                    bytes,
                    fixtures.Select((entry, index) => entry with { Atom = atoms[index] }).ToArray());
            })
            .ToArray();
        entries = sources.SelectMany(static source => source.Entries).ToArray();
        ledger ??= Ledger(entries, atomizer);
        var files = new List<RawRepositoryEntry>
        {
            new(
                TheoryAtomizerDataLoader.DataPath,
                // rulesBytes 覆盖时不触发 DigestionTestSupport.RulesBytes 的 canonical 文件读取(`??` 惰性求值)。
                ImmutableArray.CreateRange(rulesBytes ?? DigestionTestSupport.RulesBytes)),
        };
        AddLedgerFiles(files, ledger);
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

        var environment = new ProductionCliEnvironment(
                "/repo",
                new FakeRepositoryGateway(
                    RawChangeSet.Create(Array.Empty<string>()),
                RawRepositorySnapshot.Create(files),
                null),
            new FakeLeanReportSource(leanReport ?? CurrentLeanReport(entries)),
            new FakeScribeEmissionVerifier(scribeEmissions ?? VerifiedScribeEmissions.Empty));
        return environment.DigestStatus(arguments ?? ["--formalize-candidates"]);
    }

    private static byte[] ValidReceipt(EntryFixture entry) =>
        DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId,
            "D5/S0/Synthetic/Receipt." + entry.AtomId.Replace('-', '_'),
            new DigestionFormalizationSignature(
                entry.AtomId.Replace('-', '_'),
                "theorem",
                "statement-v1"),
            entry.Atom.Fingerprints.RawSha256,
            entry.Atom.Fingerprints.RawSha256)).ToArray();

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
        string status = "",
        string atomizer = AtomizerRegistry.PzgId,
        DigestionCoverDisposition? coverDisposition = null)
    {
        var source = Encoding.UTF8.GetBytes(
            status is UnterminatedPlainClosedMarker or UnterminatedClosedMarker
            ? $"# Synthetic\n\n**{kind} {number}**{status}"
            : $"# Synthetic\n\n**{kind} {number}**{status}。{body}\n");
        var rules = string.Equals(atomizer, AtomizerRegistry.GenericId, StringComparison.Ordinal)
            ? TheoryAtomizerRules.None
            : DigestionTestSupport.Rules;
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizer, source, rules).Claims);
        return new EntryFixture(
            sourceId,
            atomId,
            atom,
            coverageGids ?? [],
            migration,
            truth,
            coverDisposition);
    }

    private static BackfillInventoryDocument Ledger(
        IReadOnlyList<EntryFixture> entries,
        string atomizer = AtomizerRegistry.PzgId)
    {
        return BackfillInventoryDocument.Create(
            entries
                .GroupBy(static entry => entry.SourceId, StringComparer.Ordinal)
                .Select(source => new DigestionLedgerSource(
                    source.Key,
                    $"synthetic/{source.Key}.md",
                    atomizer,
                    [],
                    GenreRegistryProjection.Available(
                        string.Equals(atomizer, AtomizerRegistry.GenericId, StringComparison.Ordinal)
                            ? GenreRegistryCheck.NoGenreRegistry
                            : GenreRegistryCheck.Collected([])),
                    source.Select(entry => new DigestionLedgerEntry(
                        entry.SourceId,
                        $"synthetic/{entry.SourceId}.md",
                        atomizer,
                        entry.AtomId,
                        entry.Atom.Fingerprints,
                        ImmutableArray.CreateRange(entry.CoverageGids),
                        new DigestionReceipts(
                            [],
                            [],
                            [],
                            [],
                            null,
                            CoverDisposition: entry.CoverDisposition),
                        new DigestionStatus(
                            Migration(entry.Migration),
                            Truth(entry.Truth)),
                        entry.Atom.Fingerprints.RawSha256))
                        .ToImmutableArray()))
                .ToImmutableArray(),
            []);
    }

    private static void AddLedgerFiles(
        ICollection<RawRepositoryEntry> files,
        BackfillInventoryDocument ledger)
    {
        foreach (var source in ledger.RequireDigestionSources())
        {
            files.Add(new RawRepositoryEntry(
                $"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(source)));
            foreach (var entry in source.Entries)
            {
                var state = DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
                    + "-"
                    + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
                files.Add(new RawRepositoryEntry(
                    $"{BackfillInventoryLoader.RootPath}{source.SourceId}/{state}/{entry.AtomId}.yaml",
                    BackfillInventoryWriter.WriteAtom(entry)));
            }
        }

    }

    private static DigestionMigrationState Migration(string value) => value switch
    {
        "residual" => DigestionMigrationState.Residual,
        "partial" => DigestionMigrationState.Partial,
        "absorbed" => DigestionMigrationState.Absorbed,
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };

    private static DigestionTruthState Truth(string value) => value switch
    {
        "closed" => DigestionTruthState.Closed,
        "tail" => DigestionTruthState.Tail,
        "open" => DigestionTruthState.Open,
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };

    private sealed record EntryFixture(
        string SourceId,
        string AtomId,
        DigestionAtom Atom,
        string[] CoverageGids,
        string Migration,
        string Truth,
        DigestionCoverDisposition? CoverDisposition);

    private sealed record SourceFixture(
        string SourceId,
        ImmutableArray<byte> RawBytes,
        EntryFixture[] Entries);
}
