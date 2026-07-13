using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record BackfillTicketReference(string CaseId, string Gid);

internal sealed class BackfillInventoryDocument
{
    private readonly IReadOnlyDictionary<string, object?> root;

    internal BackfillInventoryDocument(IReadOnlyDictionary<string, object?> root)
    {
        this.root = root;
    }

    internal IReadOnlyDictionary<string, object?> Root => root;

    internal ImmutableArray<BackfillTicketReference> RequireTickets()
    {
        if (!root.TryGetValue("ticket_index", out var rawTicketIndex)
            || rawTicketIndex is not List<object?> ticketIndex)
        {
            throw new FormatException("ticket_index must be a list");
        }

        var tickets = ImmutableArray.CreateBuilder<BackfillTicketReference>();
        foreach (var rawTicket in ticketIndex)
        {
            if (rawTicket is not Dictionary<string, object?> ticket
                || ticket.GetValueOrDefault("case_id") is not string caseId
                || ticket.GetValueOrDefault("gid") is not string gid)
            {
                throw new FormatException("ticket_index entries must contain scalar case_id and gid values");
            }

            tickets.Add(new BackfillTicketReference(caseId, gid));
        }

        return tickets.ToImmutable();
    }

    internal ImmutableArray<string> RequireReferencedGids()
    {
        if (!root.TryGetValue("sources", out var rawSources) || rawSources is not List<object?> sources)
        {
            throw new FormatException("sources must be a list");
        }

        var gids = ImmutableArray.CreateBuilder<string>();
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var rawSource in sources)
        {
            if (rawSource is not Dictionary<string, object?> source
                || source.GetValueOrDefault("entries") is not List<object?> entries)
            {
                throw new FormatException("sources must contain entry lists");
            }

            foreach (var rawEntry in entries)
            {
                if (rawEntry is not Dictionary<string, object?> entry
                    || entry.GetValueOrDefault("disposition") is not string disposition)
                {
                    throw new FormatException("source entries must contain scalar dispositions");
                }

                if (seen.Add(disposition))
                {
                    gids.Add(disposition);
                }
            }
        }

        foreach (var ticket in RequireTickets())
        {
            if (seen.Add(ticket.Gid))
            {
                gids.Add(ticket.Gid);
            }
        }

        return gids.ToImmutable();
    }
}

internal static class BackfillInventoryLoader
{
    internal static BackfillInventoryDocument Load(string text)
    {
        if (YamlSubsetParser.Parse(text) is not Dictionary<string, object?> root)
        {
            throw new FormatException("BACKFILL top-level YAML value must be a mapping");
        }

        return new BackfillInventoryDocument(root);
    }
}
