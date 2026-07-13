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
}
