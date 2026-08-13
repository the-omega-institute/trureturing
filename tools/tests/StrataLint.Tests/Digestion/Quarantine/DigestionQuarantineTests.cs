using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionQuarantineTests
{
    private const string AtomId = "fixture-atom";
    private const string Digest = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string Quarantine = """
        quarantine:
          justification: interpretive statement has no machine predicate
          reentry_condition: typed predicate or frozen witness
        """;

    [Theory]
    [InlineData("justification: interpretive statement has no machine predicate", "reentry_condition")]
    [InlineData("reentry_condition: typed predicate or frozen witness", "justification")]
    public void LoaderRejectsQuarantineMissingARequiredField(
        string presentField,
        string missingField)
    {
        var quarantine = "quarantine:\n  " + presentField;

        var error = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.Load(LegacyLedger(Atom(AtomId, quarantine)))
                .RequireDigestionEntries());

        Assert.Contains(missingField, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void LoaderRoundTripsTypedQuarantineWithoutChangingExistingReceiptSemantics()
    {
        var document = BackfillInventoryLoader.Load(LegacyLedger(Atom(AtomId, Quarantine)));
        var entry = Assert.Single(document.RequireDigestionEntries());

        var atomBytes = BackfillInventoryWriter.WriteAtom(entry);
        var atomText = Encoding.UTF8.GetString(atomBytes.AsSpan());

        Assert.Contains(Indent(Quarantine, 2), atomText, StringComparison.Ordinal);
        Assert.Equal(
            entry with { ReceiptSyntax = null },
            Assert.Single(BackfillInventoryLoader.Load(DirectorySnapshot(atomText))
                .RequireDigestionEntries()));
    }

    [Fact]
    public void LoaderRejectsQuarantineWhenCoverageGidsContainAMachineFormStatement()
    {
        var atom = Atom(AtomId, Quarantine).Replace(
            "coverage_gids: []",
            "coverage_gids:\n  - D5/S0/Carrier/Probe.probe",
            StringComparison.Ordinal);

        var error = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.Load(LegacyLedger(atom)).RequireDigestionEntries());

        Assert.Contains("machine-form", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DirectoryLoaderRejectsQuarantineWhenFormalizationMarkerExists()
    {
        var marker = FormalizationMarker();
        var snapshot = DirectorySnapshot(
            Atom(AtomId, Quarantine),
            (DigestionFormalizationReceipt.RootPath + AtomId
                + DigestionFormalizationReceipt.PathSuffix, marker.ToArray()));

        var error = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(snapshot));

        Assert.Contains("machine-form", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void LegacySnapshotLoaderRejectsQuarantineWhenFormalizationMarkerExists()
    {
        var snapshot = DigestionTestSupport.Snapshot(
        [
            (BackfillInventoryLoader.RelativePath,
                Encoding.UTF8.GetBytes(LegacyLedger(Atom(AtomId, Quarantine)))),
            (DigestionFormalizationReceipt.RootPath + AtomId
                + DigestionFormalizationReceipt.PathSuffix,
                FormalizationMarker()),
        ]);

        var error = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(snapshot));

        Assert.Contains("machine-form", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DiskRootLoaderRejectsQuarantineWhenFormalizationMarkerExists()
    {
        using var temporary = new TemporaryDirectory();
        WriteSnapshot(temporary.Path, DirectorySnapshot(
            Atom(AtomId, Quarantine),
            (DigestionFormalizationReceipt.RootPath + AtomId
                + DigestionFormalizationReceipt.PathSuffix,
                FormalizationMarker())));

        var error = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadRoot(temporary.Path));

        Assert.Contains("machine-form", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ResidualSummaryListsQuarantinedItemsOutsideMainCounts()
    {
        var ledger = BackfillInventoryLoader.Load(LegacyLedger(
            Atom("atom-main", string.Empty, "proof-one", "proof-two"),
            Atom("atom-quarantined", Quarantine, "semantic-one", "semantic-two")));
        var entries = ledger.RequireDigestionEntries()
            .Select(static entry => new DigestionEntryEvaluation(
                entry,
                DigestionReceiptAlignment.Seen,
                entry.ProjectedStatus,
                false,
                entry.Receipts.UnresolvedSubitems
                    .Select(static item => new DigestionGap("unresolved-subitem", item))
                    .ToImmutableArray()))
            .ToImmutableArray();

        var summary = DigestResidualSummary.Render(new DigestionLedgerEvaluation(entries, []));

        var expected = """
            # Echo Residual Summary

            - unresolved_subitems: 2
            - mother_residual_atom_ids: 1

            ## quarantined residuals

            - quarantined_subitems: 2
            - mother_quarantined_atom_ids: 1

            Quarantined residual atoms:

            - `fixture-source/atom-quarantined` (2)
              - justification: `interpretive statement has no machine predicate`
              - reentry_condition: `typed predicate or frozen witness`
              - `semantic-one`
              - `semantic-two`

            ## cross-volume shared residues

            - shared_residue_names: 0
            - host_atoms: 0

            Shared residue hosts: none.

            ## `fixture-source`

            - unresolved_subitems: 2
            - mother_residual_atom_ids: 1

            Mother residual atoms:

            - `atom-main` (2)
              - `proof-one`
              - `proof-two`
            """ + "\n";
        Assert.Equal(expected, summary);
    }

    private static string LegacyLedger(params string[] atoms) =>
        "schema_version: 3\n"
        + "ledger: theory-digestion-v1\n"
        + "sources:\n"
        + "  - source_id: fixture-source\n"
        + "    path: docs/source.md\n"
        + "    atomizer: none\n"
        + "    entries:\n"
        + string.Concat(atoms.Select(static atom => LedgerEntry(atom) + "\n"))
        + "ticket_index: []\n";

    private static string Atom(
        string atomId,
        string quarantine,
        params string[] unresolvedSubitems)
    {
        var unresolved = unresolvedSubitems.Length == 0
            ? "unresolved_subitems: []"
            : "unresolved_subitems:\n"
                + string.Join('\n', unresolvedSubitems.Select(static item => "  - " + item));
        var quarantineBlock = string.IsNullOrEmpty(quarantine)
            ? string.Empty
            : "\n" + Indent(quarantine, 2);
        return $"atom_id: {atomId}\n"
            + $"ast_path: fixture/{atomId}\n"
            + "fingerprints:\n"
            + $"  raw_sha256: {Digest}\n"
            + $"  normalized_sha256: {Digest}\n"
            + $"cas_ref: {Digest}\n"
            + "coverage_gids: []\n"
            + "receipts:\n"
            + "  coverage: []\n"
            + "  scribe: []\n"
            + Indent(unresolved, 2)
            + quarantineBlock
            + "\nstatus:\n"
            + "  migration: residual\n"
            + "  truth: open";
    }

    private static RepositorySnapshot DirectorySnapshot(
        string atom,
        params (string Path, byte[] Bytes)[] additional)
    {
        var files = new List<(string Path, byte[] Bytes)>
        {
            ($"{BackfillInventoryLoader.RootPath}fixture-source/source.toml", Encoding.UTF8.GetBytes("""
                source_id = "fixture-source"
                path = "docs/source.md"
                atomizer = "none"
                """)),
            ($"{BackfillInventoryLoader.RootPath}fixture-source/residual-open/{AtomId}.yaml",
                Encoding.UTF8.GetBytes(ToDirectoryAtom(atom))),
            (BackfillInventoryLoader.TicketIndexPath, []),
        };
        files.AddRange(additional);
        return DigestionTestSupport.Snapshot([.. files]);
    }

    private static byte[] FormalizationMarker() =>
        DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            AtomId,
            "D5/S0/Carrier/Probe.probe",
            new DigestionFormalizationSignature("probe", "theorem", "True"),
            Digest,
            Digest)).ToArray();

    private static void WriteSnapshot(string root, RepositorySnapshot snapshot)
    {
        foreach (var (path, file) in snapshot.Files)
        {
            var outputPath = Path.Combine(root, path.Value.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
            File.WriteAllBytes(outputPath, file.RawBytes.AsSpan());
        }
    }

    private static string LedgerEntry(string atom)
    {
        var lines = atom.Split('\n');
        return "      - " + lines[0]
            + string.Concat(lines.Skip(1).Select(static line => "\n        " + line));
    }

    private static string ToDirectoryAtom(string atom)
    {
        if (!atom.StartsWith("atom_id: ", StringComparison.Ordinal))
        {
            return atom;
        }

        var firstLineEnd = atom.IndexOf('\n');
        var statusStart = atom.IndexOf("\nstatus:\n", StringComparison.Ordinal);
        return atom[(firstLineEnd + 1)..statusStart] + "\n";
    }

    private static string Indent(string value, int spaces)
    {
        var padding = new string(' ', spaces);
        var lines = value.Split('\n');
        return padding + lines[0]
            + string.Concat(lines.Skip(1).Select(line => "\n" + padding + line));
    }
}
