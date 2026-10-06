using System.Text;
using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Cli;

internal sealed record DigestionQueryArguments(string AtomId, string[] Sources)
{
    internal static DigestionQueryArguments Parse(IReadOnlyList<string> arguments, string command)
    {
        string? atomId = null;
        var sources = new List<string>();
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count || string.IsNullOrWhiteSpace(arguments[index + 1])) throw Invalid();
            switch (arguments[index])
            {
                case "--atom-id" when atomId is null: atomId = arguments[index + 1]; break;
                case "--source": sources.Add(arguments[index + 1]); break;
                default: throw Invalid();
            }
        }
        if (atomId is null || !DigestionFingerprint.IsCanonicalSha256("sha256:" + atomId)) throw Invalid();
        return new(atomId, sources.Distinct(StringComparer.Ordinal).ToArray());

        DigestionAtomContextException Invalid() => new(DigestionAtomContextError.ARGUMENTS_INVALID,
            $"USAGE: StrataLint {command} --atom-id ATOM_ID [--source SOURCE_ID_OR_PATH ...]");
    }
}

// Search current paths first. Only matching records and their source metadata
// enter the snapshot; references may bring in records from another source.
internal static partial class DigestionQuerySelection
{
    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadAtom(
        IRepositoryGateway repository, string atomId, IReadOnlyList<string>? selectors = null)
        => ReadAtoms(repository, [atomId], selectors);

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadAtoms(
        IRepositoryGateway repository, IReadOnlyList<string> atomIds, IReadOnlyList<string>? selectors = null)
    {
        if (atomIds.Count == 0) return Load(RawRepositorySnapshot.Create([]));
        var ids = atomIds.ToHashSet(StringComparer.Ordinal);
        var scope = selectors is { Count: > 0 }
            ? ResolveSources(repository, selectors).Select(source => Literal(BackfillInventoryLoader.RootPath + source)).ToArray()
            : atomIds.Select(id => $":(glob){BackfillInventoryLoader.RootPath}*/*/{id}.yaml").ToArray();
        var matches = repository.SearchCurrentPaths(scope).Where(IsAtomPath)
            .Where(path => ids.Contains(Path.GetFileNameWithoutExtension(path))).ToArray();
        if (matches.Length == 0) return Load(RawRepositorySnapshot.Create([]));
        var paths = matches.Concat(matches.Select(MetadataPath)).Distinct(StringComparer.Ordinal).Select(Literal).ToArray();
        return Load(repository.ReadCurrent(paths));
    }

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadChains(
        IRepositoryGateway repository,
        (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) current,
        IEnumerable<string>? roots = null, bool allowMissing = false)
    {
        var pending = (roots ?? current.Document.RequireDigestionEntries()
            .SelectMany(static entry => entry.Receipts.ChainAtoms)).ToArray();
        var visited = new HashSet<string>(StringComparer.Ordinal);
        var raw = current.Raw;
        var document = current.Document;
        var casPaths = new HashSet<string>(StringComparer.Ordinal);
        while (pending.Length > 0)
        {
            var frontier = pending.Where(visited.Add).ToArray();
            foreach (var id in frontier)
                if (!DigestionFingerprint.IsCanonicalSha256("sha256:" + id))
                    throw new FormatException($"invalid chain atom_id: {id}");
            var byId = document.RequireDigestionEntries().ToLookup(static entry => entry.AtomId, StringComparer.Ordinal);
            var missing = frontier.Where(id => !byId.Contains(id)).ToArray();
            if (missing.Length > 0)
            {
                var referenced = ReadAtoms(repository, missing);
                raw = Merge(raw, referenced.Raw);
                document = Load(raw).Document;
                byId = document.RequireDigestionEntries().ToLookup(static entry => entry.AtomId, StringComparer.Ordinal);
            }
            var next = new List<string>();
            foreach (var id in frontier)
            {
                var entries = byId[id].ToArray();
                if (entries.Length != 1 && allowMissing)
                {
                    casPaths.Add(DigestionCasStore.RootPath + id);
                    continue;
                }
                if (entries.Length != 1) throw new FormatException($"chain atom_id={id} count={entries.Length}");
                casPaths.Add(CasPath(entries[0]));
                next.AddRange(entries[0].Receipts.ChainAtoms);
            }
            pending = next.ToArray();
        }
        if (casPaths.Count > 0) raw = Merge(raw, repository.ReadCurrent(casPaths.Order(StringComparer.Ordinal).ToArray()));
        return Load(raw);
    }

    internal static string[] ResolveSources(IRepositoryGateway repository, IReadOnlyList<string> selectors)
    {
        var result = new HashSet<string>(StringComparer.Ordinal);
        foreach (var selector in selectors)
        {
            if (!RepoPath.TryCreate(selector, out _)) throw new FormatException($"invalid source selector: {selector}");
            if (!selector.Contains('/'))
            {
                var path = BackfillInventoryLoader.RootPath + selector + "/source.toml";
                var selected = Load(repository.ReadCurrent([Literal(path)])).Document.RequireDigestionSources();
                if (selected.Length != 1) throw new FormatException($"source selector is absent: {selector}");
                result.Add(selected[0].SourceId);
                continue;
            }
            var metadata = repository.ReadCurrent([$":(glob){BackfillInventoryLoader.RootPath}*/source.toml"]);
            var matches = metadata.Entries.Where(entry => entry.Path.EndsWith("/source.toml", StringComparison.Ordinal))
                .Where(entry => MatchesSourcePath(entry, selector)).Select(entry => SourceId(entry.Path)).ToArray();
            if (matches.Length != 1) throw new FormatException($"source selector={selector} count={matches.Length}");
            result.Add(matches[0]);
        }
        return result.Order(StringComparer.Ordinal).ToArray();
    }

    internal static bool MatchesSourcePath(RawRepositoryEntry entry, string path)
    {
        try
        {
            var model = TomlSerializer.Deserialize<TomlTable>(Encoding.UTF8.GetString(entry.Bytes.AsSpan()));
            return model is not null && model.TryGetValue("path", out var value) && value is string sourcePath && sourcePath == path;
        }
        catch (Exception error) when (error is FormatException or ArgumentException or TomlException) { return false; }
    }

    internal static bool IsAtomPath(string path) => path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
        && path.EndsWith(".yaml", StringComparison.Ordinal);

    internal static string SourceId(string path) => path[BackfillInventoryLoader.RootPath.Length..].Split('/')[0];
    private static string MetadataPath(string atomPath) => BackfillInventoryLoader.RootPath + SourceId(atomPath) + "/source.toml";

    internal static string Literal(string path) => ":(literal)" + path;

    internal static string CasPath(DigestionLedgerEntry entry) =>
        DigestionFingerprint.IsCanonicalSha256(entry.CasRef)
            ? DigestionCasStore.RootPath + entry.CasRef[7..]
            : throw new FormatException($"atom {entry.AtomId} cas_ref is not canonical: {entry.CasRef}");

    internal static RawRepositorySnapshot Merge(RawRepositorySnapshot current, RawRepositorySnapshot extra)
    {
        var entries = current.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        foreach (var entry in extra.Entries)
        {
            if (entries.TryGetValue(entry.Path, out var previous) && !previous.Bytes.AsSpan().SequenceEqual(entry.Bytes.AsSpan()))
                throw new FormatException($"input changed during digestion query: {entry.Path}");
            entries[entry.Path] = entry;
        }
        return RawRepositorySnapshot.Create(entries.Values);
    }

    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) Load(RawRepositorySnapshot raw)
    {
        var snapshot = SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure => throw new FormatException(failure.Message),
        };
        var document = raw.Entries.Any(static entry => entry.Path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal))
            ? BackfillInventoryLoader.LoadForDigestion(snapshot) : BackfillInventoryDocument.Create([], []);
        return (raw, snapshot, document);
    }
}
