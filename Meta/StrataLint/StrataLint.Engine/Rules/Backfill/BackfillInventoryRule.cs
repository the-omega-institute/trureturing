using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class BackfillInventoryRule
{
    private const string BackfillPath = BackfillInventoryLoader.RelativePath;
    private const string PendingContractInventoryVersion = "m0-protected-v1";

    private static readonly Regex CasePattern = new(
        "^D5-T[0-9]{4}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex TaskDeclarationPattern = new(
        "TASK (?<case>D5-T[0-9]{4})",
        RegexOptions.CultureInvariant);
    private static readonly Regex SourceIdPattern = new(
        "^[a-z0-9]+(?:[.-][a-z0-9]+)*$",
        RegexOptions.CultureInvariant);
    private static readonly Regex AtomIdPattern = new(
        "^[A-Za-z0-9]+(?:[.-][A-Za-z0-9]+)*$",
        RegexOptions.CultureInvariant);

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        if (!context.Current.TryGetFile(BackfillPath, out var file))
        {
            return [new RuleFinding(BackfillPath, "required governance document is missing")];
        }

        BackfillInventoryDocument document;
        try
        {
            document = BackfillInventoryLoader.Load(file.Text);
        }
        catch (FormatException exception)
        {
            return [new RuleFinding(BackfillPath, exception.Message)];
        }

        var root = document.Root;

        // pending-contract(step 3): schema 2 must keep the origin/dev SL-016 verdict unchanged.
        if (document.SchemaVersion != BackfillInventoryLoader.SchemaVersion)
        {
            return EvaluateSchema2(context, root);
        }

        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        if (!root.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                ["schema_version", "ledger", "sources", "ticket_index"]))
        {
            findings.Add(new RuleFinding(BackfillPath, "BACKFILL top-level keys are not canonical"));
        }

        ImmutableArray<DigestionLedgerSource> sources;
        try
        {
            sources = document.RequireDigestionSources();
        }
        catch (FormatException exception)
        {
            findings.Add(new RuleFinding(BackfillPath, exception.Message));
            sources = default;
        }

        if (!sources.IsDefault)
        {
            ValidateDigestionEntries(
                context,
                document,
                sources,
                sources.SelectMany(static source => source.Entries).ToImmutableArray(),
                findings);
        }

        root.TryGetValue("ticket_index", out var ticketIndex);
        ValidateTicketIndex(context.Current, ticketIndex, findings);
        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> EvaluateSchema2(
        RuleEvaluationContext context,
        IReadOnlyDictionary<string, object?> root)
    {
        if (!root.TryGetValue("schema_version", out var schema)
            || schema is not int version
            || version != BackfillInventoryLoader.PendingContractSchemaVersion
            || !root.TryGetValue("inventory", out var inventory)
            || inventory is not string inventoryName
            || !string.Equals(inventoryName, PendingContractInventoryVersion, StringComparison.Ordinal))
        {
            return [new RuleFinding(
                BackfillPath,
                $"BACKFILL must use schema_version 2 and inventory {PendingContractInventoryVersion}")];
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
            ValidateSchema2Source(context.Current, context.Policy, rawSource, seenIds, seenPaths, findings);
        }

        root.TryGetValue("ticket_index", out var ticketIndex);
        ValidateTicketIndex(context.Current, ticketIndex, findings);
        return findings.ToImmutable();
    }

    private static void ValidateSchema2Source(
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
            ValidateSchema2Disposition(snapshot, disposition, sourcePath, anchor, findings);
        }
    }

    private static void ValidateSchema2Disposition(
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

    private static void ValidateDigestionEntries(
        RuleEvaluationContext context,
        BackfillInventoryDocument document,
        ImmutableArray<DigestionLedgerSource> sources,
        ImmutableArray<DigestionLedgerEntry> entries,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (sources.Length == 0)
        {
            findings.Add(new RuleFinding(BackfillPath, "digestion ledger must contain at least one source"));
            return;
        }

        var seenSourceIds = new HashSet<string>(StringComparer.Ordinal);
        var seenPaths = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var source in sources)
        {
            if (!seenSourceIds.Add(source.SourceId))
            {
                findings.Add(new RuleFinding(BackfillPath, $"duplicate source_id: {source.SourceId}"));
            }

            if (!SourceIdPattern.IsMatch(source.SourceId))
            {
                findings.Add(new RuleFinding(BackfillPath, $"invalid source_id: {source.SourceId}"));
            }

            if (source.Entries.Length == 0)
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {source.SourceId} must contain at least one atomic entry"));
            }

            if (!RepoPath.TryCreate(source.SourcePath, out var sourcePath)
                || !context.Policy.GovernanceDocuments.Contains(sourcePath))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {source.SourceId} has an invalid governance path"));
            }
            else
            {
                if (!context.Current.TryGetFile(source.SourcePath, out _))
                {
                    findings.Add(new RuleFinding(BackfillPath, $"source path is dangling: {source.SourcePath}"));
                }

                if (Path.GetFileName(source.SourcePath).Contains(' '))
                {
                    findings.Add(new RuleFinding(
                        BackfillPath,
                        $"source filename contains spaces: {source.SourcePath}"));
                }
            }

            if (source.Atomizer is not ("gict-v1" or "pzg-v1" or "none"))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {source.SourceId} has unknown atomizer {source.Atomizer}"));
            }

            if (seenPaths.TryGetValue(source.SourcePath, out var priorSource))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"duplicate source path: {source.SourcePath} ({priorSource}, {source.SourceId})"));
            }
            else
            {
                seenPaths.Add(source.SourcePath, source.SourceId);
            }
        }

        if (entries.Length == 0)
        {
            return;
        }

        var seenAtomIds = new HashSet<string>(StringComparer.Ordinal);
        foreach (var entry in entries)
        {
            if (!seenAtomIds.Add(entry.AtomId))
            {
                findings.Add(new RuleFinding(BackfillPath, $"duplicate atom_id: {entry.AtomId}"));
            }

            if (!AtomIdPattern.IsMatch(entry.AtomId))
            {
                findings.Add(new RuleFinding(BackfillPath, $"invalid atom_id: {entry.AtomId}"));
            }

            if (entry.CoverageGids.Distinct(StringComparer.Ordinal).Count() != entry.CoverageGids.Length)
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"entry {entry.AtomId} has duplicate coverage GIDs"));
            }

            foreach (var gidText in entry.CoverageGids)
            {
                if (!Gid.TryParse(gidText, out var gid))
                {
                    findings.Add(new RuleFinding(
                        BackfillPath,
                        $"entry {entry.AtomId} has invalid coverage GID {gidText}"));
                }
                else if (!context.Current.TryGetFile(gid.Path.Value, out _))
                {
                    findings.Add(new RuleFinding(
                        BackfillPath,
                        $"entry {entry.AtomId} coverage target is absent: {gidText}"));
                }
            }
        }

        if (findings.Count > 0)
        {
            return;
        }

        try
        {
            var evaluation = DigestionStatusEvaluator.Evaluate(
                document,
                context.Current,
                context.Lean,
                context.VerifiedScribeEmissions);
            foreach (var finding in evaluation.Findings)
            {
                findings.Add(new RuleFinding(BackfillPath, finding));
            }
        }
        catch (FormatException exception)
        {
            findings.Add(new RuleFinding(BackfillPath, exception.Message));
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
