using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FormalizeCandidatesTests
{
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
            status: "〔closed;数值证书 n ≤ 2×10⁴〕");
        var plain = Entry(
            "source",
            "plain-closed",
            "定理",
            "7.2",
            status: "〔closed〕");
        var proved = Entry(
            "source",
            "proved-closed",
            "定理",
            "7.3",
            body: "陈述。\n\n*证明*。完整推导。证毕。",
            status: "〔closed〕");

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
        Assert.Equal("数值证书 n ≤ 2×10⁴", withheld.GetProperty("status_qualifier").GetString());
    }

    private static CommandResult Run(
        IReadOnlyList<EntryFixture> entries,
        bool includeCas = true,
        bool driftCas = false,
        string? ledger = null)
    {
        ledger ??= Ledger(entries);
        var files = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText(BackfillInventoryLoader.RelativePath, ledger),
        };
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

        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                RawRepositorySnapshot.Create(files),
                null),
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(null));
        return environment.DigestStatus(["--formalize-candidates"]);
    }

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
        var source = Encoding.UTF8.GetBytes($"# Synthetic\n\n**{kind} {number}**{status}。{body}\n");
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
}
