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
        var theoryPaths = changes.Paths.Where(path =>
            HistoricalTheoryPaths.IsTheoryDocument(path) && current.Files.ContainsKey(path))
            .Select(static path => ":(literal)" + path.Value).ToArray();
        if (theoryPaths.Length > 0)
            currentRaw = AddInputs(currentRaw, repository.ReadCurrent(theoryPaths));

        return currentRaw;
    }

    private static bool NeedsBody(string path) =>
        !HistoricalTheoryPaths.IsAuxiliaryData(RepoPath.CreateKnown(path));

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
