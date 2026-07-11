using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class BackfillInventoryRule
{
    private const string BackfillPath = "Meta/BACKFILL.yaml";
    private const string InventoryVersion = "m0-protected-v1";

    private static readonly Regex CasePattern = new(
        "^D5-T[0-9]{4}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex TaskDeclarationPattern = new(
        "TASK (?<case>D5-T[0-9]{4})",
        RegexOptions.CultureInvariant);

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        if (!context.Current.TryGetFile(BackfillPath, out var file))
        {
            return [new RuleFinding(BackfillPath, "required governance document is missing")];
        }

        Dictionary<string, object?> root;
        try
        {
            root = (Dictionary<string, object?>)YamlSubsetParser.Parse(file.Text);
        }
        catch (FormatException exception)
        {
            return [new RuleFinding(BackfillPath, exception.Message)];
        }

        if (!root.TryGetValue("schema_version", out var schema)
            || schema is not int version
            || version != 2
            || !root.TryGetValue("inventory", out var inventory)
            || inventory is not string inventoryName
            || !string.Equals(inventoryName, InventoryVersion, StringComparison.Ordinal))
        {
            return [new RuleFinding(
                BackfillPath,
                $"BACKFILL must use schema_version 2 and inventory {InventoryVersion}")];
        }

        if (!root.TryGetValue("sources", out var rawSources) || rawSources is not List<object?> sources)
        {
            return [new RuleFinding(BackfillPath, "sources must be a list")];
        }

        if (sources.Count == 0)
        {
            return [new RuleFinding(BackfillPath, "sources must contain at least one source")];
        }

        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        if (!root.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                ["schema_version", "inventory", "sources", "ticket_index"]))
        {
            findings.Add(new RuleFinding(BackfillPath, "BACKFILL top-level keys are not canonical"));
        }

        var seenIds = new HashSet<string>(StringComparer.Ordinal);
        var seenPaths = new HashSet<string>(StringComparer.Ordinal);
        foreach (var rawSource in sources)
        {
            ValidateSource(context.Current, context.Policy, rawSource, seenIds, seenPaths, findings);
        }

        root.TryGetValue("ticket_index", out var ticketIndex);
        ValidateTicketIndex(context.Current, ticketIndex, findings);
        return findings.ToImmutable();
    }

    private static void ValidateSource(
        RepositorySnapshot snapshot,
        ValidatedPolicy policy,
        object? rawSource,
        HashSet<string> seenIds,
        HashSet<string> seenPaths,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (rawSource is not Dictionary<string, object?> source)
        {
            findings.Add(new RuleFinding(BackfillPath, "each source must be a mapping"));
            return;
        }

        if (!source.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(["id", "path", "entries"]))
        {
            findings.Add(new RuleFinding(BackfillPath, "source keys are not canonical"));
        }

        source.TryGetValue("id", out var rawId);
        if (rawId is not string sourceId || string.IsNullOrWhiteSpace(sourceId))
        {
            findings.Add(new RuleFinding(BackfillPath, "each source needs an id"));
            sourceId = "<invalid>";
        }
        else if (!seenIds.Add(sourceId))
        {
            findings.Add(new RuleFinding(BackfillPath, $"duplicate source id: {sourceId}"));
        }

        source.TryGetValue("path", out var rawPath);
        if (rawPath is not string sourcePath
            || !RepoPath.TryCreate(sourcePath, out var sourceRepoPath)
            || !policy.GovernanceDocuments.Contains(sourceRepoPath))
        {
            findings.Add(new RuleFinding(BackfillPath, $"source {sourceId} has an invalid governance path"));
            return;
        }

        if (!seenPaths.Add(sourcePath))
        {
            findings.Add(new RuleFinding(BackfillPath, $"duplicate source path: {sourcePath}"));
        }

        if (!snapshot.TryGetFile(sourcePath, out _))
        {
            findings.Add(new RuleFinding(BackfillPath, $"source path is dangling: {sourcePath}"));
        }

        source.TryGetValue("entries", out var rawEntries);
        if (rawEntries is not List<object?> entries || entries.Count == 0)
        {
            findings.Add(new RuleFinding(BackfillPath, $"source {sourcePath} has no entries"));
            return;
        }

        var seenAnchors = new HashSet<string>(StringComparer.Ordinal);
        foreach (var rawEntry in entries)
        {
            if (rawEntry is not Dictionary<string, object?> entry)
            {
                findings.Add(new RuleFinding(BackfillPath, $"source {sourcePath} has a non-mapping entry"));
                continue;
            }

            if (entry.Keys.Any(static key => key is not ("anchor" or "disposition")))
            {
                findings.Add(new RuleFinding(BackfillPath, $"source {sourcePath} entry keys are not canonical"));
            }

            if (!entry.TryGetValue("anchor", out var rawAnchor)
                || rawAnchor is not string anchor
                || string.IsNullOrWhiteSpace(anchor))
            {
                findings.Add(new RuleFinding(BackfillPath, $"source {sourcePath} entry needs an anchor"));
                continue;
            }

            if (!seenAnchors.Add(anchor))
            {
                findings.Add(new RuleFinding(BackfillPath, $"duplicate source anchor: {sourcePath}#{anchor}"));
            }

            entry.TryGetValue("disposition", out var disposition);
            ValidateDisposition(snapshot, disposition, sourcePath, anchor, findings);
        }
    }

    private static void ValidateDisposition(
        RepositorySnapshot snapshot,
        object? disposition,
        string sourcePath,
        string anchor,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (disposition is not string gidText)
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                $"source {sourcePath}#{anchor} needs a disposition"));
            return;
        }

        if (!Gid.TryParse(gidText, out var gid) || !snapshot.TryGetFile(gid.Path.Value, out _))
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                $"dangling disposition {gidText}: canonical target is absent"));
        }
    }

    private static void ValidateTicketIndex(
        RepositorySnapshot snapshot,
        object? rawTicketIndex,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (rawTicketIndex is not List<object?> ticketIndex)
        {
            findings.Add(new RuleFinding(BackfillPath, "ticket_index must be a list"));
            return;
        }

        var tickets = new Dictionary<string, RepositoryFile>(StringComparer.Ordinal);
        foreach (var rawTicket in ticketIndex)
        {
            if (rawTicket is not Dictionary<string, object?> ticket
                || !ticket.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(["case_id", "gid"]))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    "ticket_index entry must contain only case_id and gid"));
                continue;
            }

            ticket.TryGetValue("case_id", out var rawCaseId);
            ticket.TryGetValue("gid", out var rawGid);
            if (rawCaseId is not string caseId
                || !CasePattern.IsMatch(caseId)
                || rawGid is not string gidText)
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    "ticket_index entry has an invalid case_id or gid"));
                continue;
            }

            if (!Gid.TryParse(gidText, out var gid)
                || !gid.Path.Value.EndsWith(".lean", StringComparison.Ordinal)
                || !snapshot.Files.TryGetValue(gid.Path, out var target))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"dangling ticket {caseId}: ticket target Lean file is absent"));
                continue;
            }

            if (!tickets.TryAdd(caseId, target))
            {
                findings.Add(new RuleFinding(BackfillPath, $"duplicate ticket case: {caseId}"));
            }
        }

        foreach (var (caseId, target) in tickets.OrderBy(static item => item.Key, StringComparer.Ordinal))
        {
            var declarations = TaskDeclarationPattern.Matches(target.Text)
                .Select(static match => match.Groups["case"].Value);
            if (!declarations.Contains(caseId, StringComparer.Ordinal))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"ticket {caseId} target does not declare TASK {caseId}: {target.Path.Value}"));
            }
        }

        var frontierCases = snapshot.Files
            .Where(static item => item.Key.Value.StartsWith("D5/X_Frontier/", StringComparison.Ordinal)
                && item.Key.Value.EndsWith(".lean", StringComparison.Ordinal))
            .SelectMany(static item => TaskDeclarationPattern.Matches(item.Value.Text))
            .Select(static match => match.Groups["case"].Value)
            .ToHashSet(StringComparer.Ordinal);
        var missing = frontierCases.Where(caseId => !tickets.ContainsKey(caseId)).Order(StringComparer.Ordinal).ToArray();
        if (missing.Length > 0)
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                "frontier TASK cases are missing from ticket_index: " + string.Join(", ", missing)));
        }
    }
}
