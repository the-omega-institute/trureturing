using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal sealed class FakeRepositoryGateway(
    RawChangeSet changes,
    RawRepositorySnapshot? current,
    RawRepositorySnapshot? baseline,
    Func<FrozenRevisionIdentity>? currentRevisionResolver = null,
    Func<string, RawChangeSet>? changesForBase = null,
    Func<RawRepositorySnapshot>? currentReader = null,
    Func<string, RawRepositorySnapshot>? revisionReader = null)
    : IRepositoryGateway
{
    internal int ReadCount { get; private set; }

    internal int ReadCurrentCount { get; private set; }

    internal List<string> ReadRevisionCalls { get; } = [];

    internal List<string> ReadChangesCalls { get; } = [];

    internal int WholeTreeReadCount { get; private set; }

    internal List<IReadOnlyList<string>> ScopedCurrentReads { get; } = [];
    internal List<IReadOnlyList<string>> CurrentPathSearches { get; } = [];

    internal int CurrentRevisionResolutionCount { get; private set; }

    public AdmissionTopologyOutcome InspectAdmissionTopology() =>
        throw new InvalidOperationException("topology should not be inspected");

    public PreparedRepository Prepare(string? protectedBase) => new("baseline", changes);

    public FrozenRevisionIdentity ResolveFrozenRevision(string revision)
    {
        var algorithm = revision.Length == 40 ? "git-sha1:" : "git-sha256:";
        return new FrozenRevisionIdentity(
            revision,
            algorithm + revision,
            algorithm + new string('b', revision.Length));
    }

    public FrozenRevisionIdentity ResolveCurrentRevision()
    {
        CurrentRevisionResolutionCount++;
        return currentRevisionResolver?.Invoke()
            ?? ResolveFrozenRevision(new string('a', 40));
    }

    public RawRepositorySnapshot ReadCurrent()
    {
        WholeTreeReadCount++;
        return ReadWholeCurrent();
    }

    public RawRepositorySnapshot ReadCurrent(IReadOnlyList<string> paths)
    {
        ScopedCurrentReads.Add(paths);
        return Scoped(ReadWholeCurrent(), paths);
    }

    public IReadOnlyList<string> SearchCurrentPaths(IReadOnlyList<string> paths)
    {
        CurrentPathSearches.Add(paths);
        return Scoped(ReadWholeCurrent(), paths).Entries.Select(static entry => entry.Path).ToArray();
    }

    public RawRepositorySnapshot ReadRevision(string revision)
    {
        WholeTreeReadCount++;
        return ReadWholeRevision(revision);
    }

    private RawRepositorySnapshot ReadWholeCurrent()
    {
        ReadCount++;
        ReadCurrentCount++;
        return WithAtomizerData(
            currentReader?.Invoke()
            ?? current
            ?? throw new InvalidOperationException("current snapshot should not be read"));
    }

    private RawRepositorySnapshot ReadWholeRevision(string revision)
    {
        ReadCount++;
        ReadRevisionCalls.Add(revision);
        return WithAtomizerData(
            revisionReader?.Invoke(revision)
            ?? baseline ?? throw new InvalidOperationException("baseline snapshot should not be read"));
    }

    public RawChangeSet ReadCurrentChanges() => changes;

    public RawChangeSet ReadChanges(string revision)
    {
        ReadChangesCalls.Add(revision);
        return changesForBase?.Invoke(revision) ?? changes;
    }

    // A path selects itself and, as a directory, everything under it.
    private static RawRepositorySnapshot Scoped(RawRepositorySnapshot snapshot, IReadOnlyList<string> paths) =>
        RawRepositorySnapshot.Create(snapshot.Entries.Where(entry => paths.Any(path =>
            GitRepositoryGateway.MatchesPathSelection(entry.Path, path))));

    private static RawRepositorySnapshot WithAtomizerData(RawRepositorySnapshot snapshot) =>
        snapshot.Entries.Any(static entry => entry.Path == TheoryAtomizerDataLoader.DataPath)
            ? snapshot
            : RawRepositorySnapshot.Create(snapshot.Entries.Add(new RawRepositoryEntry(
                TheoryAtomizerDataLoader.DataPath,
                ImmutableArray.CreateRange(DigestionTestSupport.RulesBytes))));
}
