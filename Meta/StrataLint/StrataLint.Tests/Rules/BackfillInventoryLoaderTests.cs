using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class BackfillInventoryLoaderTests
{
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
