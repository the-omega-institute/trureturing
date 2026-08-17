using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record BackfillInventoryValidationContext(
    RepositorySnapshot Current,
    RepositorySnapshot Baseline,
    ValidatedPolicy Policy,
    AcceptedLeanClosure Lean,
    VerifiedScribeEmissions? VerifiedScribeEmissions,
    RawChangeSet? Changes = null);

internal static class BackfillInventoryRule
{
    private const string BackfillPath = BackfillInventoryLoader.RelativePath;

    private static readonly Regex SourceIdPattern = new(
        "^[a-z0-9]+(?:[.-][a-z0-9]+)*$",
        RegexOptions.CultureInvariant);
    private static readonly Regex AtomIdPattern = new(
        "^[A-Za-z0-9]+(?:[.-][A-Za-z0-9]+)*$",
        RegexOptions.CultureInvariant);

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
        => Evaluate(context, changes: null);

    internal static ImmutableArray<RuleFinding> EvaluateCandidateDelta(RuleEvaluationContext context)
        => Evaluate(context, context.Changes);

    internal static bool IsAffectedBy(RuleEvaluationContext context)
    {
        foreach (var path in context.Changes.Paths)
        {
            if (BackfillInventoryLoader.IsCanonicalPath(path.Value)
                || DigestionCasStore.IsCanonicalPath(path.Value)
                || path.Value == BackfillInventoryLoader.RelativePath
                || path.Value == TheoryAtomizerDataLoader.DataPath
                || path.Value is "Meta/registry.yaml" or "Meta/domains.yaml"
                || path.Value.StartsWith("D5/", StringComparison.Ordinal)
                    && path.Value.EndsWith(".lean", StringComparison.Ordinal)
                || path.Value.StartsWith("Evidence/D5/", StringComparison.Ordinal)
                || path.Value.StartsWith("Blueprint/", StringComparison.Ordinal)
                || path.Value.StartsWith(
                    "tools/Authorizations/digestion-tail/",
                    StringComparison.Ordinal)
                || FrozenLedgerDeltaPredicate.IsEnvironmentInput(path.Value)
                || context.Policy.GovernanceDocuments.Contains(path))
            {
                return true;
            }
        }

        return false;
    }

    private static ImmutableArray<RuleFinding> Evaluate(
        RuleEvaluationContext context,
        RawChangeSet? changes)
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
                context.VerifiedScribeEmissions,
                changes),
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
                     context.Baseline,
                     context.Changes))
        {
            findings.Add(new RuleFinding(BackfillPath, finding));
        }

        var root = document.Root;
        if (!root.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                ["schema_version", "ledger", "sources"]))
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

        return findings.ToImmutable();
    }

    /// <summary>
    /// The inverse of the source-path check above, and the reason it exists: that one asks
    /// whether a declared source names a governed document, this one asks whether a
    /// governed theory document has a source. Without it a volume can sit in the tree
    /// undigested with nothing red — a dangling reference in the direction nobody checks,
    /// which produces no symptom because the thing that is missing is the reader.
    /// </summary>
    private static void ValidateTheoryCoverage(
        BackfillInventoryValidationContext context,
        IEnumerable<string> declaredPaths,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        var declared = declaredPaths.ToHashSet(StringComparer.Ordinal);
        foreach (var path in context.Policy.GovernanceDocuments
                     .Select(static path => path.Value)
                     .Where(static path => path.StartsWith(
                         DigestionOpaquePathPolicy.TheoryRootPath,
                         StringComparison.Ordinal))
                     .Where(path => !declared.Contains(path))
                     .Order(StringComparer.Ordinal))
        {
            findings.Add(new RuleFinding(
                BackfillPath,
                $"theory document '{path}' has no digestion source: run make ingest, "
                + "which registers it with the default atomizer"));
        }
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

        ValidateTheoryCoverage(context, seenPaths.Keys, findings);

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

        var hasStructuralFindings = findings.Count > 0;
        // CAS integrity is part of SL-016 itself, so it must run even when another
        // receipt-shape finding below would otherwise return before status derivation.
        // The result is threaded into the alignment pass below, which used to recompute it.
        var casEvaluation = DigestionCasStore.Evaluate(
            document,
            context.Current,
            context.Changes);
        foreach (var finding in casEvaluation.Findings)
        {
            findings.Add(new RuleFinding(BackfillPath, finding));
        }

        if (hasStructuralFindings)
        {
            return;
        }

        try
        {
            var evaluation = DigestionStatusEvaluator.Evaluate(
                document,
                context.Current,
                context.Lean,
                context.VerifiedScribeEmissions,
                LoadBaselineDocument(context.Baseline),
                baselineSnapshot: context.Baseline,
                casEvaluation: casEvaluation,
                changes: context.Changes);
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

    private static BackfillInventoryDocument LoadBaselineDocument(RepositorySnapshot baseline)
    {
        try
        {
            return BackfillInventoryLoader.LoadBaseline(baseline);
        }
        catch (FormatException exception) when (
            string.Equals(exception.Message, "required governance document is missing", StringComparison.Ordinal))
        {
            throw new FormatException("baseline digestion ledger is missing");
        }
    }

}
