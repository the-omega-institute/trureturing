using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class BackfillInventoryLoaderTests
{
    [Fact]
    public void SnapshotLegacyShapeDelegatesByteIdenticallyToTextLoader()
    {
        var fields = LoaderEntryFields().ToHashSet(StringComparer.Ordinal);
        fields.Remove("boundary");
        var text = EntryFixture(fields);

        var direct = BackfillInventoryLoader.Load(text);
        var dispatched = BackfillInventoryLoader.Load(Snapshot((BackfillInventoryLoader.RelativePath, text)));

        Assert.Equal(
            BackfillInventoryWriter.Write(direct).ToArray(),
            BackfillInventoryWriter.Write(dispatched).ToArray());
    }

    [Fact]
    public void DirectoryShapeProjectsTwoSourcesAtomsAndTicketIndex()
    {
        var snapshot = Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            Source("epsilon-v0.1", "docs/epsilon.md", "none"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            Atom("epsilon-v0.1", "partial-closed", "epsilon-atom", "theorem/epsilon"),
            (BackfillInventoryLoader.TicketIndexPath, "D5-T0098 = \"D5/X_Frontier/SyntheticDelta\"\n"));

        var document = BackfillInventoryLoader.Load(snapshot);

        Assert.Equal(["delta-v0.1", "epsilon-v0.1"],
            document.RequireDigestionSources().Select(static source => source.SourceId).ToArray());
        Assert.Equal(["delta-atom", "epsilon-atom"],
            document.RequireDigestionEntries().Select(static entry => entry.AtomId).ToArray());
        var ticket = Assert.Single(document.RequireTickets());
        Assert.Equal("D5-T0098", ticket.CaseId);
        Assert.Equal("D5/X_Frontier/SyntheticDelta", ticket.Gid);
        Assert.Collection(
            document.RequireDigestionEntries(),
            entry =>
            {
                Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
                Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
            },
            entry =>
            {
                Assert.Equal(DigestionMigrationState.Partial, entry.ProjectedStatus.Migration);
                Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
            });
    }

    [Fact]
    public void DirectoryAtomWriterPreservesLiveOptionalReceipts()
    {
        var atom = Atom("delta-v0.1", "absorbed-tail", "delta-atom", "theorem/delta");
        var authorizationPath = "Meta/Digestion/tail-authorizations/delta-atom.json";
        var authorizationSha = "sha256:1111111111111111111111111111111111111111111111111111111111111111";
        var liveAtom = atom.Text.Replace(
            "  chain_atoms: []\n  tail_authorization: null",
            "  chain_atoms:\n    - predecessor-atom\n"
            + $"  tail_authorization:\n    path: {authorizationPath}\n    sha256: {authorizationSha}",
            StringComparison.Ordinal);
        var document = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, liveAtom),
            (BackfillInventoryLoader.TicketIndexPath, "")));

        var written = Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(
            Assert.Single(document.RequireDigestionEntries())).AsSpan());
        var roundTripped = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, written),
            (BackfillInventoryLoader.TicketIndexPath, "")));

        var receipts = Assert.Single(roundTripped.RequireDigestionEntries()).Receipts;
        Assert.Equal(["predecessor-atom"], receipts.ChainAtoms.ToArray());
        Assert.Equal(authorizationPath, receipts.TailAuthorization?.Path);
        Assert.Equal(authorizationSha, receipts.TailAuthorization?.Sha256);
    }

    [Fact]
    public void BothStorageShapesAreRejected()
    {
        var text = EntryFixture(LoaderEntryFields().ToHashSet(StringComparer.Ordinal));
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (BackfillInventoryLoader.RelativePath, text),
            Source("delta-v0.1", "docs/delta.md", "none"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            (BackfillInventoryLoader.TicketIndexPath, ""))));

        Assert.Equal("legacy and directory digestion ledgers cannot coexist", exception.Message);
    }

    [Fact]
    public void DiskRootRejectsBothStorageShapesWithSnapshotMessage()
    {
        using var temporary = new TemporaryDirectory();
        var legacyPath = Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(legacyPath)!);
        File.WriteAllText(
            legacyPath,
            EntryFixture(LoaderEntryFields().ToHashSet(StringComparer.Ordinal)),
            new UTF8Encoding(false));
        var source = Source("delta-v0.1", "docs/delta.md", "none");
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        DirectoryLedgerTestSupport.Write(temporary.Path, new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [source.Path] = source.Text,
            [atom.Path] = atom.Text,
            [BackfillInventoryLoader.TicketIndexPath] = string.Empty,
        });

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadRoot(temporary.Path));

        Assert.Equal("legacy and directory digestion ledgers cannot coexist", exception.Message);
    }

    [Fact]
    public void NeitherStorageShapeUsesExistingMissingMessage()
    {
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot()));

        Assert.Equal("required governance document is missing", exception.Message);
    }

    [Fact]
    public void DirectoryAtomWithNoncanonicalEntryKeyIsRejected()
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, atom.Text + "unexpected: value\n"),
            (BackfillInventoryLoader.TicketIndexPath, ""))));

        Assert.Equal("source delta-v0.1 entry keys are not canonical", exception.Message);
    }

    [Fact]
    public void CanonicalAtomWithoutOwningSourceMetadataIsRejected()
    {
        var path = $"{BackfillInventoryLoader.RootPath}zeta-v0.1/residual-open/zeta-atom.yaml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            (path, Atom("zeta-v0.1", "residual-open", "zeta-atom", "theorem/zeta").Text),
            (BackfillInventoryLoader.TicketIndexPath, ""))));

        Assert.Equal($"backfill atom is not owned by exactly one source: {path}", exception.Message);
    }

    [Theory]
    [InlineData("source_id = [\"delta-v0.1\"]\npath = \"docs/delta.md\"\natomizer = \"none\"\n")]
    [InlineData("source_id = \"delta-v0.1\"\npath = [\"docs/delta.md\", \"docs/epsilon.md\"]\natomizer = \"none\"\n")]
    [InlineData("source_id = \"delta-v0.1\"\npath = \"docs/delta.md\"\natomizer = []\n")]
    [InlineData("source_id = \"delta-v0.1\" trailing\npath = \"docs/delta.md\"\natomizer = \"none\"\n")]
    public void SourceMetadataRequiresExactlyOneQuotedScalarPerIdentityField(string metadata)
    {
        var path = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (path, metadata),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            (BackfillInventoryLoader.TicketIndexPath, ""))));

        Assert.Equal($"source metadata identity fields must be single quoted strings: {path}", exception.Message);
    }

    [Fact]
    public void SourceMetadataPreservesAcknowledgedStaleArray()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var document = BackfillInventoryLoader.Load(Snapshot(
            (sourcePath, "source_id = \"delta-v0.1\"\npath = \"docs/delta.md\"\natomizer = \"none\"\nacknowledged_stale = [\"old-one\", \"old-two\"]\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            (BackfillInventoryLoader.TicketIndexPath, "")));

        Assert.Equal(
            ["old-one", "old-two"],
            Assert.Single(document.RequireDigestionSources()).AcknowledgedStale.ToArray());
    }

    [Fact]
    public void SourceMetadataAllowsEmptyAcknowledgedStaleArray()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var document = BackfillInventoryLoader.Load(Snapshot(
            (sourcePath, "source_id = \"delta-v0.1\"\npath = \"docs/delta.md\"\natomizer = \"none\"\nacknowledged_stale = []\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            (BackfillInventoryLoader.TicketIndexPath, "")));

        Assert.Empty(Assert.Single(document.RequireDigestionSources()).AcknowledgedStale);
    }

    [Theory]
    [InlineData("\"old-one\"")]
    [InlineData("[\"\"]")]
    [InlineData("[\"   \"]")]
    [InlineData("[\"old-one\", \"\"]")]
    public void AcknowledgedStaleRequiresNonemptyQuotedStringArray(string encoded)
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (sourcePath, $"source_id = \"delta-v0.1\"\npath = \"docs/delta.md\"\natomizer = \"none\"\nacknowledged_stale = {encoded}\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            (BackfillInventoryLoader.TicketIndexPath, ""))));

        Assert.Equal($"acknowledged_stale must be a quoted string array without blank elements: {sourcePath}", exception.Message);
    }

    [Theory]
    [InlineData("not-an-assignment")]
    [InlineData("D5-T0098 = unquoted")]
    [InlineData("D5-T0098 = \"D5/X_Frontier/SyntheticDelta\" = \"extra\"")]
    [InlineData("D5-T0098 = \"D5/X_Frontier/SyntheticDelta\" trailing")]
    [InlineData("D5-T0098 = \"D5/X_Frontier/SyntheticDelta\", \"D5/X_Frontier/Other\"")]
    [InlineData("D5-T0098 = \"D5/X_Frontier/Synthetic\"Delta\"")]
    public void IllegalTicketIndexIsRejected(string ticketIndex)
    {
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            (BackfillInventoryLoader.TicketIndexPath, ticketIndex + "\n"))));

        Assert.Contains("digestion ticket index", exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("residual-open", "delta-atom.txt")]
    [InlineData("pending-open", "delta-atom.yaml")]
    [InlineData("residual-frozen", "delta-atom.yaml")]
    [InlineData("residual-open/nested", "delta-atom.yaml")]
    public void NoncanonicalDirectoryFilesAreRejected(string state, string fileName)
    {
        var path = $"{BackfillInventoryLoader.RootPath}delta-v0.1/{state}/{fileName}";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (path, "value: invalid\n"),
            (BackfillInventoryLoader.TicketIndexPath, ""))));

        Assert.Equal($"noncanonical digestion ledger path: {path}", exception.Message);
    }

    [Theory]
    [InlineData(BackfillInventoryLoader.TicketIndexPath)]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/source.toml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/residual-open/atom-0dca.yaml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/partial-closed/atom-0f28.yaml")]
    [InlineData("Meta/Digestion/backfill/epsilon-v0.1/absorbed-tail/atom.yaml")]
    public void CanonicalDigestionLedgerPathsAreRecognized(string path)
        => Assert.True(BackfillInventoryLoader.IsCanonicalPath(path));

    [Theory]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/residual-open/atom.txt")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/pending-open/atom.yaml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/residual-frozen/atom.yaml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/residual-open/nested/atom.yaml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/notes.toml")]
    [InlineData("Meta/Digestion/ticket-index.yaml")]
    [InlineData("Meta/BACKFILL.yaml")]
    public void NoncanonicalDigestionLedgerPathsAreRejected(string path)
        => Assert.False(BackfillInventoryLoader.IsCanonicalPath(path));

    // chain_atoms / tail_authorization 在 dev 现有记录里均为空,故目录形态允许省略;
    // 活值仍由 loader 与 writer 完整保留,不得静默丢弃。
    [Fact]
    public void ReceiptsWithoutRetiredLegacyKeysAreAccepted()
    {
        var fields = LoaderEntryFields().ToHashSet(StringComparer.Ordinal);
        fields.Remove("boundary");
        Assert.True(TryLoadEntry(EntryFixture(fields).Replace(
            "              chain_atoms: []\n              tail_authorization: null\n", string.Empty)));
    }

    [Fact]
    public void MissingCasRefIsRejected()
    {
        var fields = LoaderEntryFields().ToHashSet(StringComparer.Ordinal);
        fields.Remove("cas_ref");
        fields.Remove("boundary");

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.Load(EntryFixture(fields)).RequireDigestionEntries());

        Assert.Equal("source synthetic-source entry keys are not canonical", exception.Message);
    }

    [Fact]
    public void CasRefRoundTripsCanonically()
    {
        var text = """
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: synthetic-source
                path: docs/source.md
                atomizer: synthetic-v1
                entries:
                  - atom_id: synthetic-atom
                    ast_path: theorem/1.1
                    fingerprints:
                      raw_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
                      normalized_sha256: sha256:1111111111111111111111111111111111111111111111111111111111111111
                    cas_ref: sha256:0000000000000000000000000000000000000000000000000000000000000000
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
                    status:
                      migration: residual
                      truth: open
            ticket_index: []
            """;

        var document = BackfillInventoryLoader.Load(text);
        var entry = Assert.Single(document.RequireDigestionEntries());
        var roundTripped = BackfillInventoryLoader.Load(
            Encoding.UTF8.GetString(BackfillInventoryWriter.Write(document).AsSpan()));

        Assert.Equal(
            "sha256:0000000000000000000000000000000000000000000000000000000000000000",
            entry.CasRef);
        Assert.Equal(entry.CasRef, Assert.Single(roundTripped.RequireDigestionEntries()).CasRef);
    }

    [Fact]
    public void ProjectsReferencesFromSyntheticBackfill()
    {
        const string yaml = """
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: synthetic-source
                path: docs/synthetic.md
                atomizer: none
                entries:
                  - atom_id: synthetic-atom
                    boundary:
                      ast_path: manual/synthetic
                      start_byte: 0
                      end_byte: 1
                    fingerprints:
                      raw_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
                      normalized_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
                    cas_ref: sha256:0000000000000000000000000000000000000000000000000000000000000000
                    coverage_gids:
                      - D5/X_Frontier/SyntheticSourceTarget
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
                    status:
                      migration: partial
                      truth: open
            ticket_index:
              - case_id: D5-T0099
                gid: D5/X_Frontier/SyntheticTicketTarget
            """;

        var inventory = BackfillInventoryLoader.Load(yaml);
        var ticket = Assert.Single(inventory.RequireTickets());

        Assert.Equal(3, inventory.Root["schema_version"]);
        Assert.Equal("synthetic-atom", Assert.Single(inventory.RequireDigestionEntries()).AtomId);
        Assert.Equal("D5-T0099", ticket.CaseId);
        Assert.Equal("D5/X_Frontier/SyntheticTicketTarget", ticket.Gid);
        Assert.Equal(
            ["D5/X_Frontier/SyntheticSourceTarget", "D5/X_Frontier/SyntheticTicketTarget"],
            inventory.RequireReferencedGids().ToArray());
    }

    [Fact]
    public void ExpandedSourceProjectsStructuralIdentityAndStaleAcknowledgments()
    {
        const string yaml = """
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: synthetic-source
                path: docs/synthetic.md
                atomizer: synthetic-v1
                acknowledged_stale:
                  - synthetic-stale
                entries:
                  - atom_id: synthetic-stale
                    ast_path: theorem/1.1
                    fingerprints:
                      raw_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
                      normalized_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
                    cas_ref: sha256:0000000000000000000000000000000000000000000000000000000000000000
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
                    status:
                      migration: residual
                      truth: open
            ticket_index: []
            """;

        var inventory = BackfillInventoryLoader.Load(yaml);
        var source = Assert.Single(inventory.RequireDigestionSources());
        var entry = Assert.Single(source.Entries);

        Assert.Equal(["synthetic-stale"], source.AcknowledgedStale.ToArray());
        Assert.Equal("theorem/1.1", entry.AstPath);
        Assert.Null(entry.Boundary);

        var roundTripped = BackfillInventoryLoader.Load(
            System.Text.Encoding.UTF8.GetString(BackfillInventoryWriter.Write(inventory).AsSpan()));
        Assert.Empty(roundTripped.RequireTickets());
    }

    [Theory]
    [InlineData("[]")]
    [InlineData("null")]
    [InlineData("~")]
    [InlineData("0")]
    [InlineData("+1")]
    [InlineData("01")]
    [InlineData("|")]
    [InlineData("|-")]
    [InlineData("|+")]
    [InlineData(">")]
    [InlineData(">-")]
    [InlineData(">+")]
    public void CanonicalWriterQuotesStringScalarsThatTheParserWouldCoerce(string atomId)
    {
        var yaml = $$"""
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: synthetic-source
                path: docs/synthetic.md
                atomizer: synthetic-v1
                acknowledged_stale: []
                entries:
                  - atom_id: '{{atomId}}'
                    ast_path: theorem/1.1
                    fingerprints:
                      raw_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
                      normalized_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
                    cas_ref: sha256:0000000000000000000000000000000000000000000000000000000000000000
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
                    status:
                      migration: residual
                      truth: open
            ticket_index: []
            """;
        var inventory = BackfillInventoryLoader.Load(yaml);

        var written = System.Text.Encoding.UTF8.GetString(
            BackfillInventoryWriter.Write(inventory).AsSpan());
        var roundTripped = BackfillInventoryLoader.Load(written);
        var source = Assert.Single(roundTripped.RequireDigestionSources());

        Assert.Equal(atomId, Assert.Single(source.Entries).AtomId);
        Assert.Contains($"atom_id: '{atomId}'", written, StringComparison.Ordinal);
    }

    [Fact]
    public void CanonicalWriterRoundTripsTheCurrentLedgerByteExact()
    {
        var root = TestRepositoryLayout.FindRoot();
        var path = Path.Combine(root, BackfillInventoryLoader.RelativePath);
        if (File.Exists(path))
        {
            var expected = File.ReadAllBytes(path);

            var actual = BackfillInventoryWriter.Write(
                BackfillInventoryLoader.Load(File.ReadAllText(path)));

            Assert.Equal(expected, actual.ToArray());
            return;
        }

        // 目录形态没有单文件字节可对照;互逆契约改为当前台账在 Write∘Load
        // 上的字节不动点。
        var first = BackfillInventoryWriter.Write(BackfillInventoryLoader.LoadRoot(root));
        var second = BackfillInventoryWriter.Write(
            BackfillInventoryLoader.Load(System.Text.Encoding.UTF8.GetString(first.AsSpan())));

        Assert.Equal(first.ToArray(), second.ToArray());
    }

    [Fact]
    public void CanonicalLedgerE2StoresEveryReceiptPreimageInCas()
    {
        var root = TestRepositoryLayout.FindRoot();
        var document = BackfillInventoryLoader.LoadRoot(root);
        var entries = document.RequireDigestionEntries();

        Assert.NotEmpty(entries);
        Assert.Contains(document.RequireDigestionSources(), static source =>
            AtomizerRegistry.IsRegistered(source.Atomizer));
        Assert.Empty(entries
            .Select(entry => (
                Entry: entry,
                Path: Path.Combine(
                    root,
                    (DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..])
                    .Replace('/', Path.DirectorySeparatorChar))))
            .Where(static item => !File.Exists(item.Path))
            .Select(static item => $"{item.Entry.SourceId}/{item.Entry.AtomId}"));
        Assert.Empty(entries
            .Select(entry => (
                Entry: entry,
                Path: Path.Combine(
                    root,
                    (DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..])
                    .Replace('/', Path.DirectorySeparatorChar))))
            .Where(static item => File.Exists(item.Path)
                && DigestionCasStore.Capture(File.ReadAllBytes(item.Path)).Reference
                != item.Entry.CasRef)
            .Select(static item => $"{item.Entry.SourceId}/{item.Entry.AtomId}"));
    }

    [Fact]
    public void RemarkBatchUpgradeCandidatesRemainResidualWithNamedUnresolvedClaims()
    {
        var root = TestRepositoryLayout.FindRoot();
        var entries = BackfillInventoryLoader.LoadRoot(root)
            .RequireDigestionEntries();
        string[] expectedPaths =
        [
            "remark/6.37",
            "remark/6.43",
            "remark/10.11",
            "remark/27.20",
            "remark/27.25",
            "remark/27.30",
            "remark/27.35",
            "remark/27.41",
            "remark/27.95",
        ];

        foreach (var path in expectedPaths)
        {
            var entry = Assert.Single(entries, entry => entry.AstPath == path);

            Assert.Empty(entry.CoverageGids);
            Assert.Empty(entry.Receipts.Coverage);
            Assert.Empty(entry.Receipts.Scribe);
            Assert.NotEmpty(entry.Receipts.UnresolvedSubitems);
            Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
        }
    }

    [Fact]
    public void StatementEchoForbidsRemarkClosureOfCertificatesAndTestableIdentities()
    {
        var root = TestRepositoryLayout.FindRoot();
        var echo = File.ReadAllText(Path.Combine(root, "agents", "echo-template.md"));

        Assert.Contains("Remark-closure guard", echo, StringComparison.Ordinal);
        Assert.Contains("numerical certificate", echo, StringComparison.Ordinal);
        Assert.Contains("independently testable identity", echo, StringComparison.Ordinal);
        Assert.Contains("upgrade-candidate", echo, StringComparison.Ordinal);
        Assert.Contains("retained_residual", echo, StringComparison.Ordinal);
        Assert.Contains("unresolved_subitems", echo, StringComparison.Ordinal);
    }


    private static bool TryLoadEntry(string yaml)
    {
        try
        {
            BackfillInventoryLoader.Load(yaml).RequireDigestionEntries();
            return true;
        }
        catch (FormatException)
        {
            return false;
        }
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files)
    {
        var raw = RawRepositorySnapshot.Create(
            files.Select(static file => RawRepositoryEntry.FromText(file.Path, file.Text)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static (string Path, string Text) Source(string sourceId, string path, string atomizer) =>
        ($"{BackfillInventoryLoader.RootPath}{sourceId}/source.toml",
            $"source_id = \"{sourceId}\"\npath = \"{path}\"\natomizer = \"{atomizer}\"\n");

    private static (string Path, string Text) Atom(
        string sourceId,
        string state,
        string atomId,
        string astPath) =>
        ($"{BackfillInventoryLoader.RootPath}{sourceId}/{state}/{atomId}.yaml", $$"""
            ast_path: {{astPath}}
            fingerprints:
              raw_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
              normalized_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
            cas_ref: sha256:0000000000000000000000000000000000000000000000000000000000000000
            coverage_gids: []
            receipts:
              coverage: []
              scribe: []
              unresolved_subitems: []
              chain_atoms: []
              tail_authorization: null
            """ + "\n");

    private static string[] LoaderEntryFields() =>
        BackfillInventoryDocument.EntryFieldUniverse.ToArray();

    private static string EntryFixture(IReadOnlySet<string> fields)
    {
        var entry = new StringBuilder();
        if (fields.Contains("atom_id"))
        {
            entry.AppendLine("      - atom_id: synthetic-atom");
        }
        else
        {
            entry.AppendLine("      - synthetic_placeholder: value");
        }

        if (fields.Contains("ast_path"))
        {
            entry.AppendLine("        ast_path: theorem/1.1");
        }

        if (fields.Contains("boundary"))
        {
            entry.AppendLine("        boundary:");
            entry.AppendLine("          ast_path: theorem/1.1");
            entry.AppendLine("          start_byte: 0");
            entry.AppendLine("          end_byte: 1");
        }

        if (fields.Contains("fingerprints"))
        {
            entry.AppendLine("        fingerprints:");
            entry.AppendLine("          raw_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000");
            entry.AppendLine("          normalized_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000");
        }

        if (fields.Contains("cas_ref"))
        {
            entry.AppendLine("        cas_ref: sha256:0000000000000000000000000000000000000000000000000000000000000000");
        }

        if (fields.Contains("coverage_gids"))
        {
            entry.AppendLine("        coverage_gids: []");
        }

        if (fields.Contains("receipts"))
        {
            entry.AppendLine("        receipts:");
            entry.AppendLine("          coverage: []");
            entry.AppendLine("          scribe: []");
            entry.AppendLine("          unresolved_subitems: []");
            entry.AppendLine("          chain_atoms: []");
            entry.AppendLine("          tail_authorization: null");
        }

        if (fields.Contains("status"))
        {
            entry.AppendLine("        status:");
            entry.AppendLine("          migration: residual");
            entry.AppendLine("          truth: open");
        }

        return """
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: synthetic-source
                path: docs/source.md
                atomizer: synthetic-v1
                entries:
            """ + "\n" + entry + "ticket_index: []\n";
    }
}
