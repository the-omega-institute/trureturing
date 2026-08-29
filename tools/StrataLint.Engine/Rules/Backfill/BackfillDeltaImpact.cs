namespace StrataLint.Engine;

internal sealed record BackfillDeltaImpact(
    RawChangeSet EvaluationChanges,
    bool HasAffectedEdges);

internal static class BackfillDeltaImpactResolver
{
    internal static BackfillDeltaImpact Resolve(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        BackfillInventoryDocument document,
        RawChangeSet repositoryChanges)
    {
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(repositoryChanges);

        var changedPaths = repositoryChanges.Paths
            .Select(static path => path.Value)
            .ToHashSet(StringComparer.Ordinal);
        var affectedEntryPaths = document.RequireDigestionEntries()
            .Where(entry => DirectDependencyValueChanged(
                entry,
                current,
                baseline,
                changedPaths))
            .Select(EntryPath)
            .ToHashSet(StringComparer.Ordinal);

        AddFrozenStatementDependants(
            current,
            baseline,
            document,
            repositoryChanges,
            affectedEntryPaths);

        // Raw frozen and Lean paths have historically widened one dependency change to every
        // edge. Their value changes are represented by the affected entry paths above instead.
        var evaluationEntries = repositoryChanges.Entries
            .Where(static change =>
                !FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value)
                && !(change.Path.Value.StartsWith("D5/", StringComparison.Ordinal)
                    && change.Path.Value.EndsWith(".lean", StringComparison.Ordinal)))
            .ToDictionary(static change => change.Path.Value, StringComparer.Ordinal);
        foreach (var path in affectedEntryPaths)
        {
            evaluationEntries.TryAdd(
                path,
                new RawChange(RepoPath.CreateKnown(path), RawChangeKind.Modified));
        }

        return new BackfillDeltaImpact(
            RawChangeSet.CreateWithKinds(evaluationEntries.Values.Select(static change =>
                (change.Path.Value, change.Kind))),
            affectedEntryPaths.Count > 0);
    }

    private static bool DirectDependencyValueChanged(
        DigestionLedgerEntry entry,
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        IReadOnlySet<string> changedPaths)
    {
        if (EntryPathIsInDelta(entry, changedPaths)
            || FileValueChanged(entry.SourcePath, current, baseline, changedPaths)
            || FileValueChanged(CasPath(entry), current, baseline, changedPaths)
            || entry.Receipts.TailAuthorization is { } tail
                && FileValueChanged(tail.Path, current, baseline, changedPaths)
            || changedPaths.Contains(TheoryAtomizerDataLoader.DataPath)
                && FileValueChanged(
                    TheoryAtomizerDataLoader.DataPath,
                    current,
                    baseline,
                    changedPaths))
        {
            return true;
        }

        foreach (var gid in entry.CoverageGids)
        {
            var documentGid = ScribeEmissionAttestation.DocumentGid(gid);
            if (FileValueChanged(
                    ScribeEmissionAttestation.DefinitionPath(documentGid),
                    current,
                    baseline,
                    changedPaths)
                || FileValueChanged(
                    ScribeEmissionAttestation.EmissionPath(documentGid),
                    current,
                    baseline,
                    changedPaths))
            {
                return true;
            }
        }

        return false;
    }

    private static void AddFrozenStatementDependants(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        BackfillInventoryDocument document,
        RawChangeSet repositoryChanges,
        ISet<string> affectedEntryPaths)
    {
        if (!repositoryChanges.Paths.Any(static path =>
                FrozenLedgerChangeClassifier.IsAcceptedEventPath(path.Value)))
        {
            return;
        }

        var reverseIndex = BuildCoverageReverseIndex(document);
        FrozenStatementIndex currentStatements;
        FrozenStatementIndex baselineStatements;
        try
        {
            currentStatements = FrozenStatementIndex.Load(current);
            baselineStatements = FrozenStatementIndex.Load(baseline);
        }
        catch (Exception exception) when (
            exception is FormatException or InvalidOperationException)
        {
            // Frozen-ledger shape and history have their own admission owner. An invalid
            // projection has no comparable statement value for SL-016 to propagate.
            return;
        }

        foreach (var (gidText, entryPaths) in reverseIndex)
        {
            if (!Gid.TryParse(gidText, out var gid)
                || FrozenStatementValue(currentStatements, gid)
                    == FrozenStatementValue(baselineStatements, gid))
            {
                continue;
            }

            foreach (var entryPath in entryPaths)
            {
                affectedEntryPaths.Add(entryPath);
            }
        }
    }

    private static Dictionary<string, HashSet<string>> BuildCoverageReverseIndex(
        BackfillInventoryDocument document)
    {
        var result = new Dictionary<string, HashSet<string>>(StringComparer.Ordinal);
        foreach (var entry in document.RequireDigestionEntries())
        {
            var entryPath = EntryPath(entry);
            foreach (var gid in entry.CoverageGids.Distinct(StringComparer.Ordinal))
            {
                if (!result.TryGetValue(gid, out var paths))
                {
                    paths = new HashSet<string>(StringComparer.Ordinal);
                    result.Add(gid, paths);
                }

                paths.Add(entryPath);
            }
        }

        return result;
    }

    private static string FrozenStatementValue(FrozenStatementIndex index, Gid gid) =>
        index.TryResolve(gid, out var statementId, out var message)
            ? "resolved:" + statementId!.Value
            : "unresolved:" + message;

    private static bool EntryPathIsInDelta(
        DigestionLedgerEntry entry,
        IReadOnlySet<string> changedPaths)
    {
        if (changedPaths.Contains(BackfillInventoryLoader.RelativePath))
        {
            return true;
        }

        var sourcePrefix = BackfillInventoryLoader.RootPath + entry.SourceId + "/";
        var suffix = "/" + entry.AtomId + ".yaml";
        return changedPaths.Contains(sourcePrefix + "source.toml")
            || changedPaths.Any(path =>
                path.StartsWith(sourcePrefix, StringComparison.Ordinal)
                && path.EndsWith(suffix, StringComparison.Ordinal));
    }

    private static bool FileValueChanged(
        string path,
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        IReadOnlySet<string> changedPaths)
    {
        if (!changedPaths.Contains(path))
        {
            return false;
        }

        var currentExists = current.TryGetFile(path, out var currentFile);
        var baselineExists = baseline.TryGetFile(path, out var baselineFile);
        return currentExists != baselineExists
            || currentExists
            && !currentFile!.RawBytes.AsSpan().SequenceEqual(baselineFile!.RawBytes.AsSpan());
    }

    private static string CasPath(DigestionLedgerEntry entry) =>
        DigestionFingerprint.IsCanonicalSha256(entry.CasRef)
            ? DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..]
            : string.Empty;

    private static string EntryPath(DigestionLedgerEntry entry) =>
        BackfillInventoryLoader.RootPath
        + entry.SourceId
        + "/"
        + DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
        + "-"
        + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)
        + "/"
        + entry.AtomId
        + ".yaml";
}
