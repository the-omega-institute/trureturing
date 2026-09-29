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
        ReadCount++;
        ReadCurrentCount++;
        return WithAtomizerData(
            currentReader?.Invoke()
            ?? current
            ?? throw new InvalidOperationException("current snapshot should not be read"));
    }

    public RawRepositorySnapshot ReadRevision(string revision)
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

    private static RawRepositorySnapshot WithAtomizerData(RawRepositorySnapshot snapshot) =>
        snapshot.Entries.Any(static entry => entry.Path == TheoryAtomizerDataLoader.DataPath)
            ? snapshot
            : RawRepositorySnapshot.Create(snapshot.Entries.Add(new RawRepositoryEntry(
                TheoryAtomizerDataLoader.DataPath,
                ImmutableArray.CreateRange(DigestionTestSupport.RulesBytes))));
}
