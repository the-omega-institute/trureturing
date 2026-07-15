using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class BackfillInventoryLoaderTests
{
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

    [Fact]
    public void CanonicalWriterRoundTripsTheCurrentLedgerByteExact()
    {
        var root = FindRepositoryRoot();
        var path = Path.Combine(root, BackfillInventoryLoader.RelativePath);
        var expected = File.ReadAllBytes(path);

        var actual = BackfillInventoryWriter.Write(
            BackfillInventoryLoader.Load(File.ReadAllText(path)));

        Assert.Equal(expected, actual.ToArray());
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, BackfillInventoryLoader.RelativePath)))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
