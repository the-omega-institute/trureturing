using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class BackfillInventoryLoaderTests
{
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
    public void DirectoryAtomWithNoncanonicalEntryKeyIsRejected()
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, atom.Text + "unexpected: value\n"),
            (BackfillInventoryLoader.TicketIndexPath, ""))));

        Assert.Equal("source delta-v0.1 entry keys are not canonical", exception.Message);
    }

    [Theory]
    [InlineData("ast_path")]
    [InlineData("fingerprints")]
    [InlineData("cas_ref")]
    [InlineData("coverage_gids")]
    [InlineData("receipts")]
    public void DirectoryAtomMissingCanonicalKeyIsRejected(string missingKey)
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var text = RemoveTopLevelField(atom.Text, missingKey);

        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, text),
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
    [InlineData("Meta/Digestion/backfill/delta-v0.1/source.toml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/residual-open/atom-0dca.yaml")]
    [InlineData("Meta/Digestion/backfill/delta-v0.1/partial-closed/atom-0f28.yaml")]
    [InlineData("Meta/Digestion/backfill/epsilon-v0.1/absorbed-tail/atom.yaml")]
    public void CanonicalDigestionLedgerPathsAreRecognized(string path)
        => Assert.True(BackfillInventoryLoader.IsCanonicalPath(path));

    // 工单索引路径用常量而非字面量:它在树上真实存在,抄写会触发 RepositoryPathLiteralTests。
    [Fact]
    public void TicketIndexPathIsRecognized()
        => Assert.True(BackfillInventoryLoader.IsCanonicalPath(BackfillInventoryLoader.TicketIndexPath));

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

    [Fact]
    public void MissingCasRefIsRejected()
    {
        var fields = LoaderEntryFields().ToHashSet(StringComparer.Ordinal);
        fields.Remove("cas_ref");

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.Load(EntryFixture(fields)).RequireDigestionEntries());

        Assert.Equal("source synthetic-source entry keys are not canonical", exception.Message);
    }

    [Fact]
    public void EntryAcceptanceDomainMatchesSpecificationAnchor()
    {
        var entryFields = LoaderEntryFields();
        var accepted = Enumerable.Range(0, 1 << entryFields.Length)
            .Select(mask => entryFields
                .Where((_, index) => (mask & (1 << index)) != 0)
                .ToHashSet(StringComparer.Ordinal))
            .Where(fields => TryLoadEntry(EntryFixture(fields)))
            .ToArray();
        Assert.NotEmpty(accepted);

        var required = entryFields
            .Where(field => accepted.All(fields => fields.Contains(field)))
            .Order(StringComparer.Ordinal)
            .ToArray();
        var optional = entryFields
            .Except(required, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var actual = $"required={string.Join(',', required)};"
            + $"optional={(optional.Length == 0 ? "-" : string.Join(',', optional))}";

        var root = FindRepositoryRoot();
        var specification = File.ReadAllText(
            Path.Combine(root, "docs", "develop", "spec", "golden-ledger-repo-spec.md"));
        var anchors = Regex.Matches(
            specification,
            "<!-- BACKFILL_ENTRY_ACCEPTANCE: (?<domain>[^\\r\\n]+) -->",
            RegexOptions.CultureInvariant);
        var anchor = Assert.Single(anchors.Cast<Match>());

        Assert.Equal(anchor.Groups["domain"].Value, actual);
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
                    ast_path: manual/synthetic
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
        var root = FindRepositoryRoot();
        var document = BackfillInventoryLoader.LoadDirectory(root);
        foreach (var entry in BackfillInventoryWriter.WriteDirectory(document))
        {
            var path = Path.Combine(root, entry.Path.Replace('/', Path.DirectorySeparatorChar));
            Assert.Equal(File.ReadAllBytes(path), entry.Bytes.ToArray());
        }
    }

    [Fact]
    public void DirectoryWriterEmitsCanonicalEmptyCollectionKeys()
    {
        var document = BackfillInventoryLoader.Load(Snapshot(
            Source("epsilon-v0.1", "docs/epsilon.md", "none"),
            Atom("epsilon-v0.1", "residual-open", "epsilon-atom", "theorem/epsilon"),
            (BackfillInventoryLoader.TicketIndexPath, "")));

        var atom = BackfillInventoryWriter.WriteDirectory(document)
            .Single(static entry => entry.Path.EndsWith("/epsilon-atom.yaml", StringComparison.Ordinal));
        var text = Encoding.UTF8.GetString(atom.Bytes.AsSpan());

        Assert.Contains("coverage_gids: []\n", text, StringComparison.Ordinal);
        Assert.Contains(
            "receipts:\n  coverage: []\n  scribe: []\n  unresolved_subitems: []\n",
            text,
            StringComparison.Ordinal);
    }

    [Fact]
    public void CanonicalLedgerE2StoresEveryReceiptPreimageInCas()
    {
        var root = FindRepositoryRoot();
        var document = BackfillInventoryLoader.LoadDirectory(root);
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
        var root = FindRepositoryRoot();
        var entries = BackfillInventoryLoader.LoadDirectory(root)
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
        var root = FindRepositoryRoot();
        var echo = File.ReadAllText(Path.Combine(root, "agents", "echo-template.md"));

        Assert.Contains("Remark-closure guard", echo, StringComparison.Ordinal);
        Assert.Contains("numerical certificate", echo, StringComparison.Ordinal);
        Assert.Contains("independently testable identity", echo, StringComparison.Ordinal);
        Assert.Contains("upgrade-candidate", echo, StringComparison.Ordinal);
        Assert.Contains("retained_residual", echo, StringComparison.Ordinal);
        Assert.Contains("unresolved_subitems", echo, StringComparison.Ordinal);
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (Directory.Exists(Path.Combine(current.FullName, BackfillInventoryLoader.RootPath)))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
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
            """ + "\n");

    private static string[] LoaderEntryFields() =>
        BackfillInventoryDocument.EntryFieldUniverse.ToArray();

    private static string RemoveTopLevelField(string yaml, string key)
    {
        var lines = yaml.Split('\n').ToList();
        var start = lines.FindIndex(line => line.StartsWith(key + ":", StringComparison.Ordinal));
        Assert.True(start >= 0);
        var end = start + 1;
        while (end < lines.Count
               && (lines[end].Length == 0 || char.IsWhiteSpace(lines[end][0])))
        {
            end++;
        }
        lines.RemoveRange(start, end - start);
        return string.Join('\n', lines);
    }

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
