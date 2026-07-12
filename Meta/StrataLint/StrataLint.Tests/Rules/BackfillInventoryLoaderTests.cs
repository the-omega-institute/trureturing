using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class BackfillInventoryLoaderTests
{
    [Fact]
    public void ProjectsReferencesFromSyntheticBackfill()
    {
        const string yaml = """
            schema_version: 2
            inventory: synthetic-fixture
            sources:
              - id: synthetic-source
                path: docs/synthetic.md
                entries:
                  - anchor: synthetic-anchor
                    disposition: D5/X_Frontier/SyntheticSourceTarget
            ticket_index:
              - case_id: D5-T0099
                gid: D5/X_Frontier/SyntheticTicketTarget
            """;

        var inventory = BackfillInventoryLoader.Load(yaml);
        var ticket = Assert.Single(inventory.RequireTickets());

        Assert.Equal(2, inventory.Root["schema_version"]);
        Assert.Equal("D5-T0099", ticket.CaseId);
        Assert.Equal("D5/X_Frontier/SyntheticTicketTarget", ticket.Gid);
        Assert.Equal(
            ["D5/X_Frontier/SyntheticSourceTarget", "D5/X_Frontier/SyntheticTicketTarget"],
            inventory.RequireReferencedGids().ToArray());
    }
}
