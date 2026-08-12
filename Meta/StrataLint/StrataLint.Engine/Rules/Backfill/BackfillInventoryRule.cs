using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record BackfillInventoryValidationContext(
    RepositorySnapshot Current,
    RepositorySnapshot Baseline,
    ValidatedPolicy Policy,
    AcceptedLeanClosure Lean,
    VerifiedScribeEmissions? VerifiedScribeEmissions);

internal static class BackfillInventoryRule
{
    private const string BackfillPath = BackfillInventoryLoader.RelativePath;

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
        BackfillInventoryDocument document;
        try
        {
            document = BackfillInventoryLoader.Load(context.Current);
        }
        catch (FormatException exception)
        {
            return [new RuleFinding(BackfillPath, exception.Message)];
        }

        return EvaluateDocument(
            new BackfillInventoryValidationContext(
                context.Current,
                context.ForkPoint,
                context.Policy,
                context.Lean,
                context.VerifiedScribeEmissions),
            document);
    }

    internal static ImmutableArray<RuleFinding> EvaluateDocument(
        BackfillInventoryValidationContext context,
        BackfillInventoryDocument document)
    {
        ArgumentNullException.ThrowIfNull(context);
        ArgumentNullException.ThrowIfNull(document);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var finding in DigestionCasStore.ValidateAppendOnly(
                     context.Current,
                     context.Baseline))
        {
            findings.Add(new RuleFinding(BackfillPath, finding));
        }

        var root = document.Root;
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

    private static void ValidateDigestionEntries(
        BackfillInventoryValidationContext context,
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
                // First thing a new volume hits, so the verdict carries its own remedy
                // rather than leaving the reader to find which registry field is meant.
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {source.SourceId} has an invalid governance path "
                    + $"'{source.SourcePath}': add it to governance_documents in "
                    + "Meta/registry.yaml"));
            }
            else
            {
                if (source.Atomizer == AtomizerRegistry.NoAtomizerId
                    && !context.Current.TryGetFile(source.SourcePath, out _))
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

            if (source.Atomizer != AtomizerRegistry.NoAtomizerId
                && !AtomizerRegistry.IsRegistered(source.Atomizer))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {source.SourceId} has unknown atomizer {source.Atomizer}. "
                    + "Registered atomizers: "
                    + string.Join(", ", AtomizerRegistry.RegisteredIds)
                    + "."));
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

        BackfillInventoryDocument baselineDocument;
        try
        {
            baselineDocument = LoadBaselineDocument(context.Baseline);
            var evaluation = DigestionStatusEvaluator.Evaluate(
                document,
                context.Current,
                context.Lean,
                context.VerifiedScribeEmissions,
                baselineDocument);
            foreach (var finding in evaluation.Findings)
            {
                findings.Add(new RuleFinding(BackfillPath, finding));
            }
        }
        catch (FormatException exception)
        {
            findings.Add(new RuleFinding(BackfillPath, exception.Message));
            return;
        }

        var baselineByAtomId = baselineDocument.RequireDigestionEntries()
            .ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        foreach (var entry in entries)
        {
            var priorCoverage = baselineByAtomId.TryGetValue(entry.AtomId, out var baselineEntry)
                ? baselineEntry.CoverageGids
                : ImmutableArray<string>.Empty;
            var addedCoverage = entry.CoverageGids
                .Where(gid => !priorCoverage.Contains(gid, StringComparer.Ordinal))
                .ToArray();
            if (addedCoverage.Length == 0)
            {
                continue;
            }

            try
            {
                DigestionFormalizationReceiptVerifier.RequireAuthorizedCoverage(
                    context.Baseline,
                    DigestionFormalizationReceipt.PathFor(entry.AtomId),
                    entry,
                    priorCoverage,
                    addedCoverage,
                    context.Lean.Report);
            }
            catch (Exception exception) when (exception is FormatException or InvalidOperationException)
            {
                findings.Add(new RuleFinding(BackfillPath, exception.Message));
            }
        }

        ValidateCrossAtomCoverage(
            context,
            entries,
            baselineByAtomId,
            findings);
    }

    private static void ValidateCrossAtomCoverage(
        BackfillInventoryValidationContext context,
        ImmutableArray<DigestionLedgerEntry> entries,
        IReadOnlyDictionary<string, DigestionLedgerEntry> baselineByAtomId,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        foreach (var group in entries
                     .SelectMany(entry => entry.CoverageGids.Select(gid => (Gid: gid, Entry: entry)))
                     .GroupBy(static item => item.Gid, StringComparer.Ordinal)
                     .Where(static group => group.Count() > 1))
        {
            var owners = group.Select(static item => item.Entry).ToArray();
            if (owners.All(owner =>
                    baselineByAtomId.TryGetValue(owner.AtomId, out var baselineOwner)
                    && baselineOwner.CoverageGids.Contains(group.Key, StringComparer.Ordinal)))
            {
                continue;
            }

            if (owners.Select(static entry => entry.AstPath).Distinct(StringComparer.Ordinal).Count() != 1)
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"coverage GID {group.Key} is bound to atoms with different residual paths: "
                    + string.Join(",", owners.Select(static entry => entry.AtomId))));
                continue;
            }

            foreach (var owner in owners)
            {
                if (!baselineByAtomId.TryGetValue(owner.AtomId, out var baselineOwner)
                    || !string.Equals(owner.AstPath, baselineOwner.AstPath, StringComparison.Ordinal)
                    || owner.Fingerprints != baselineOwner.Fingerprints
                    || !string.Equals(owner.CasRef, baselineOwner.CasRef, StringComparison.Ordinal))
                {
                    findings.Add(new RuleFinding(
                        BackfillPath,
                        $"shared coverage GID {group.Key} has no matching fork-point atom {owner.AtomId}"));
                    continue;
                }

                try
                {
                    DigestionFormalizationReceiptVerifier.RequireAuthorizedCoverage(
                        context.Baseline,
                        DigestionFormalizationReceipt.PathFor(owner.AtomId),
                        owner,
                        baselineOwner.CoverageGids,
                        owner.CoverageGids.Where(gid =>
                            !baselineOwner.CoverageGids.Contains(gid, StringComparer.Ordinal)),
                        context.Lean.Report);
                }
                catch (Exception exception) when (exception is FormatException or InvalidOperationException)
                {
                    findings.Add(new RuleFinding(BackfillPath, exception.Message));
                }
            }
        }
    }

    private static BackfillInventoryDocument LoadBaselineDocument(RepositorySnapshot baseline)
    {
        try
        {
            return BackfillInventoryLoader.Load(baseline);
        }
        catch (FormatException exception) when (
            string.Equals(exception.Message, "required governance document is missing", StringComparison.Ordinal))
        {
            throw new FormatException("baseline digestion ledger is missing");
        }
    }

    // Contract the compatibility branch when this protected-baseline condition becomes true:
    // !snapshot.TryGetFile(RelativePath, out _)
    // && snapshot.Files.Keys.Any(path => IsCanonicalPath(path.Value)). Then remove the legacy
    // Load(string), RelativePath, dispatch branch, and legacy tests together.

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
