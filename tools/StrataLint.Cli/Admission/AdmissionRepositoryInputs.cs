using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class AdmissionRepositoryInputs
{
    internal static RawRepositorySnapshot ReadCurrent(IRepositoryGateway repository) =>
        repository.ReadCurrentProjection(NeedsBody);

    internal static RawRepositorySnapshot ReadBaseline(IRepositoryGateway repository, string revision) =>
        repository.ReadRevisionProjection(revision, NeedsBody);

    internal static RawRepositorySnapshot ReadDeltaInputs(
        IRepositoryGateway repository, RawRepositorySnapshot currentRaw,
        RawRepositorySnapshot baselineRaw, RawChangeSet changes)
    {
        var current = Decode(currentRaw);
        var baseline = Decode(baselineRaw);
        var theoryPaths = changes.Paths.Where(path =>
            DigestionOpaquePathPolicy.IsTheoryDocument(path) && current.Files.ContainsKey(path))
            .Select(static path => DigestionQuerySelection.Literal(path.Value)).ToArray();
        if (theoryPaths.Length > 0)
            currentRaw = AddInputs(currentRaw, repository.ReadCurrent(theoryPaths));

        var atoms = new HashSet<string>(StringComparer.Ordinal);
        foreach (var selected in UtilityAdmissionRule.SelectInputPaths(current, baseline, changes))
        {
            var path = FrozenStatePath.TryToModulePath(selected.Value, out var module) ? module : selected;
            if (current.Files.TryGetValue(path, out var file)
                && RepositoryRules.TryHeader(file.Text, out var header)
                && UtilitySyntax.TryParse(header.Utility, out var utility, out _)
                && utility!.BasisTarget is { Kind: UtilityTargetKind.Atom } atom)
                atoms.Add(atom.Value);
        }
        if (atoms.Count > 0)
        {
            var paths = currentRaw.Entries.Select(static entry => entry.Path)
                .Where(BackfillInventoryLoader.IsCanonicalPath)
                .Where(path => path.EndsWith(".yaml", StringComparison.Ordinal)
                    && atoms.Contains(Path.GetFileNameWithoutExtension(path))).ToArray();
            var metadata = paths.Select(path => path[..(path.IndexOf('/',
                BackfillInventoryLoader.RootPath.Length) + 1)] + "source.toml");
            var selected = paths.Concat(metadata).Distinct(StringComparer.Ordinal)
                .Select(DigestionQuerySelection.Literal).ToArray();
            if (selected.Length > 0)
                currentRaw = AddInputs(currentRaw, repository.ReadCurrent(selected));
        }
        return currentRaw;
    }

    private static bool NeedsBody(string path) =>
        !DigestionOpaquePathPolicy.IsAuxiliaryData(RepoPath.CreateKnown(path));

    private static RawRepositorySnapshot AddInputs(RawRepositorySnapshot current, RawRepositorySnapshot selected)
    {
        var files = current.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        foreach (var entry in selected.Entries)
        {
            if (files.TryGetValue(entry.Path, out var previous)
                && previous.ContentWasRead
                && !previous.Bytes.AsSpan().SequenceEqual(entry.Bytes.AsSpan()))
                throw new InvalidOperationException($"admission input changed during selection: {entry.Path}");
            files[entry.Path] = entry;
        }
        return RawRepositorySnapshot.Create(files.Values, current.PathInventory);
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidOperationException(failure.Message),
    };
}
