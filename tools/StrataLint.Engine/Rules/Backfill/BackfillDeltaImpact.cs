namespace StrataLint.Engine;

internal sealed record BackfillDeltaImpact(
    RawChangeSet EvaluationChanges,
    RawChangeSet ReceiptVerificationChanges,
    bool HasAffectedEdges);

internal static class BackfillDeltaImpactResolver
{
    private sealed record CoverageTargetDependency(
        Gid Gid,
        RepoPath HostModule,
        string EntryPath,
        string? TargetStatementId);

    internal static BackfillDeltaImpact Resolve(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        LeanAxiomReport? report,
        BackfillInventoryDocument document,
        RawChangeSet repositoryChanges,
        Action<string>? statementResolutionObserved = null)
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

        AddCurrentResolutionDependants(
            current,
            report,
            document,
            repositoryChanges,
            affectedEntryPaths,
            statementResolutionObserved);

        // Raw frozen and Lean paths have historically widened one dependency change to every
        // edge. Their value changes are represented by the affected entry paths above instead.
        var evaluationEntries = repositoryChanges.Entries
            .Where(static change =>
                !FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value)
                && !FrozenStatePath.IsUnderRoot(change.Path.Value)
                && !(change.Path.Value.StartsWith("D5/", StringComparison.Ordinal)
                    && change.Path.Value.EndsWith(".lean", StringComparison.Ordinal)))
            .ToDictionary(static change => change.Path.Value, StringComparer.Ordinal);
        foreach (var path in affectedEntryPaths)
        {
            evaluationEntries.TryAdd(
                path,
                new RawChange(RepoPath.CreateKnown(path), RawChangeKind.Modified));
        }

        var receiptVerificationEntries = evaluationEntries
            .ToDictionary(static entry => entry.Key, static entry => entry.Value, StringComparer.Ordinal);
        foreach (var change in repositoryChanges.Entries.Where(static change =>
                     change.Path.Value.StartsWith("D5/", StringComparison.Ordinal)
                     && change.Path.Value.EndsWith(".lean", StringComparison.Ordinal)))
        {
            receiptVerificationEntries.TryAdd(change.Path.Value, change);
        }

        return new BackfillDeltaImpact(
            RawChangeSet.CreateWithKinds(evaluationEntries.Values.Select(static change =>
                (change.Path.Value, change.Kind))),
            RawChangeSet.CreateWithKinds(receiptVerificationEntries.Values.Select(static change =>
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
            || FileValueChanged(
                BackfillInventoryLoader.RootPath + entry.SourceId + "/source.toml",
                current,
                baseline,
                changedPaths)
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

    internal static bool HasPotentialStatementDependants(
        BackfillInventoryDocument document,
        RawChangeSet repositoryChanges)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(repositoryChanges);
        var changedModules = ChangedStatementModules(repositoryChanges);
        if (changedModules.Count == 0)
        {
            return false;
        }

        return BuildCoverageReverseIndex(document).Values.Any(dependencies =>
            changedModules.Contains(dependencies[0].HostModule));
    }

    private static void AddCurrentResolutionDependants(
        RepositorySnapshot current,
        LeanAxiomReport? report,
        BackfillInventoryDocument document,
        RawChangeSet repositoryChanges,
        ISet<string> affectedEntryPaths,
        Action<string>? statementResolutionObserved)
    {
        var reverseIndex = BuildCoverageReverseIndex(document);
        var changedModules = ChangedStatementModules(repositoryChanges);
        var candidates = reverseIndex
            .Where(item =>
                changedModules.Contains(item.Value[0].HostModule)
                || item.Value.Any(dependency =>
                    affectedEntryPaths.Contains(dependency.EntryPath)))
            .ToArray();
        if (candidates.Length == 0)
        {
            return;
        }

        FrozenStateCatalog frozenState;
        FrozenStatementIndex? currentStatements;
        try
        {
            frozenState = FrozenStateCatalog.Load(current);
            currentStatements = report is null
                ? null
                : FrozenStatementIndex.Create(frozenState, report);
        }
        catch (Exception exception) when (
            exception is FormatException or InvalidOperationException)
        {
            // Frozen-state shape and the Lean report have their own admission owners. An
            // invalid authority has no comparable statement value for SL-016 to propagate.
            return;
        }

        foreach (var (gidText, dependencies) in candidates)
        {
            var gid = dependencies[0].Gid;
            string? currentResolution;
            if (gid.ToTarget() is Target.Formal { Declaration: null } formal)
            {
                currentResolution = frozenState.Records.TryGetValue(formal.Path, out var frozen)
                    ? frozen.StatementId.Value
                    : null;
            }
            else if (currentStatements is null)
            {
                // Declaration statement identity is report-derived. A report-free caller has no
                // current declaration value to compare, so absence must not mean unresolved.
                continue;
            }
            else
            {
                currentResolution = currentStatements.TryResolve(
                    gid,
                    out var statementId,
                    out _)
                        ? statementId!.Value
                        : null;
            }

            statementResolutionObserved?.Invoke(gidText);
            foreach (var dependency in dependencies)
            {
                if (string.Equals(
                        dependency.TargetStatementId,
                        currentResolution,
                        StringComparison.Ordinal))
                {
                    continue;
                }

                affectedEntryPaths.Add(dependency.EntryPath);
            }
        }
    }

    private static Dictionary<string, List<CoverageTargetDependency>> BuildCoverageReverseIndex(
        BackfillInventoryDocument document)
    {
        var result = new Dictionary<string, List<CoverageTargetDependency>>(StringComparer.Ordinal);
        foreach (var entry in document.RequireDigestionEntries())
        {
            var entryPath = EntryPath(entry);
            foreach (var edge in entry.Coverage)
            {
                if (!Gid.TryParse(edge.Gid, out var gid)
                    || gid.ToTarget() is not Target.Formal formal)
                {
                    continue;
                }

                if (!result.TryGetValue(edge.Gid, out var dependencies))
                {
                    dependencies = [];
                    result.Add(edge.Gid, dependencies);
                }

                dependencies.Add(new CoverageTargetDependency(
                    gid,
                    formal.Path,
                    entryPath,
                    edge.TargetStatementId));
            }
        }

        return result;
    }

    private static HashSet<RepoPath> ChangedStatementModules(RawChangeSet repositoryChanges)
    {
        var result = new HashSet<RepoPath>();
        foreach (var path in repositoryChanges.Paths)
        {
            if (FrozenStatePath.TryToModulePath(path.Value, out var stateModule))
            {
                result.Add(stateModule);
            }
            else if (path.Value.StartsWith("D5/", StringComparison.Ordinal)
                && path.Value.EndsWith(".lean", StringComparison.Ordinal))
            {
                result.Add(path);
            }
        }

        return result;
    }

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
        return changedPaths.Any(path =>
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
