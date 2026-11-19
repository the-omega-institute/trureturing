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
    Func<string, RawRepositorySnapshot>? revisionReader = null,
    bool addSourcePolicy = true)
    : IRepositoryGateway
{
    internal int ReadCount { get; private set; }

    internal int ReadCurrentCount { get; private set; }

    internal List<string> ReadRevisionCalls { get; } = [];

    internal List<string> ReadChangesCalls { get; } = [];

    internal int WholeTreeReadCount { get; private set; }

    internal List<IReadOnlyList<string>> ScopedCurrentReads { get; } = [];
    internal List<(string Revision, IReadOnlyList<string> Paths)> ScopedRevisionReads { get; } = [];
    internal List<IReadOnlyList<string>> CurrentPathSearches { get; } = [];

    internal int CurrentRevisionResolutionCount { get; private set; }
    internal int PrepareCount { get; private set; }

    public AdmissionTopologyOutcome InspectAdmissionTopology() =>
        throw new InvalidOperationException("topology should not be inspected");

    public PreparedRepository Prepare(string? protectedBase)
    {
        PrepareCount++;
        return new("baseline", changes);
    }

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

    public RawRepositorySnapshot ReadRevision(string revision, IReadOnlyList<string> paths)
    {
        ScopedRevisionReads.Add((revision, paths));
        return Scoped(ReadWholeRevision(revision), paths);
    }

    private static RawRepositorySnapshot WithFileMap(RawRepositorySnapshot raw)
    {
        if (raw.Entries.Any(entry => entry.Path == FileMapLoader.RelativePath)) return raw;
        var files = (raw.Entries
                .Where(entry => !entry.Path.StartsWith("Meta/", StringComparison.Ordinal))
                .Select(entry => entry.Path)).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)
            .Select(path => "{ pattern = " + System.Text.Json.JsonSerializer.Serialize(path)
                + ", kind = \"data\", admission_plane = \"content\", produced_by = \"none\", consumed_by = [\"reader\"], "
                + "verified_by = [\"SnapshotDecoder\"], artifact_id = \"none\", runtime_disposition = \"committed-source\" }");
        var policy = "schema_version = 6\nfiles = [\n" + string.Join(",\n", files)
            + "\n]\n[evidence.artifact_kinds.md]\nprofile = \"opaque-text\"\nselectors = [\"result\"]\npath_selectors = [\"formal\"]\n[residence_policy]\ncase_id = \"TEST\"\ndesired = \"data-must-live-outside-tools\"\nknown_violation_count = 0\nstatus = \"closed\"\n";
        return RawRepositorySnapshot.Create(raw.Entries.Add(RawRepositoryEntry.FromText(
            FileMapLoader.RelativePath, policy)), raw.PathInventory);
    }

    private RawRepositorySnapshot ReadWholeCurrent()
    {
        ReadCount++;
        ReadCurrentCount++;
        var snapshot = currentReader?.Invoke()
            ?? current
            ?? throw new InvalidOperationException("current snapshot should not be read");
        return addSourcePolicy ? WithFileMap(snapshot) : snapshot;
    }

    private RawRepositorySnapshot ReadWholeRevision(string revision)
    {
        ReadCount++;
        ReadRevisionCalls.Add(revision);
        return (
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
            GitRepositoryGateway.MatchesPathSelection(entry.Path, path))),
            snapshot.PathInventory.IsDefault ? default : snapshot.PathInventory.Where(entry => paths.Any(path =>
                GitRepositoryGateway.MatchesPathSelection(entry.Path, path))).ToImmutableArray());

}
