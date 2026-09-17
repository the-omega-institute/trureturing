using System.Collections.Immutable;
using Tomlyn.Model;

namespace StrataLint.Engine;

internal enum FileMapAdmissionPlane
{
    Judge,
    Content,
}

internal sealed class FileMapAdmissionPlaneException(
    string code,
    string path,
    string location,
    string message) : FormatException($"Invalid FILEMAP at {location}: {code}: {message}.")
{
    internal string Code { get; } = code;

    internal string Path { get; } = path;
}

internal sealed class FileMapParseException(string location, string message, Exception? inner = null)
    : FormatException($"Invalid FILEMAP at {location}: {message}.", inner);

internal static class FileMapTomlTables
{
    internal static TomlTable[] Parse(object? value, string location, bool allowEmpty)
    {
        var tables = value switch
        {
            TomlTableArray tableArray => tableArray.Cast<TomlTable>().ToArray(),
            TomlArray array when array.All(static item => item is TomlTable) =>
                array.Cast<TomlTable>().ToArray(),
            _ => throw Invalid(location, "files must be an array containing only tables"),
        };
        if (!allowEmpty && tables.Length == 0)
        {
            throw Invalid(location, "files must contain at least one entry");
        }

        return tables;
    }

    private static FormatException Invalid(string location, string message) =>
        new($"Invalid FILEMAP at {location}: {message}.");
}

internal enum AdmissionPlaneClassification
{
    Empty,
    JudgeOnly,
    ContentOnly,
    Mixed,
}

internal sealed record AdmissionPlaneDecision(
    bool IsAdmissible,
    AdmissionPlaneClassification? Classification,
    string Code,
    string Path,
    string Message)
{
    internal bool RequiresFullEngineering()
    {
        if (!IsAdmissible || Classification is null)
        {
            throw new InvalidOperationException(
                "FULL routing requires an admissible admission-plane classification.");
        }

        return Classification is AdmissionPlaneClassification.JudgeOnly;
    }
}

internal static class AdmissionPlanePolicy
{
    internal const string FileMapPath = "Meta/FILEMAP.toml";
    internal const string MixedCode = "ADMISSION-PLANE-MIXED";

    internal static AdmissionPlaneDecision Evaluate(
        RawRepositorySnapshot candidate,
        RawRepositorySnapshot protectedBase,
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(changes);
        var endpoints = changes.Entries.Where(static change => change.Kind switch
        {
            RawChangeKind.Added or RawChangeKind.Modified or RawChangeKind.Deleted => true,
            RawChangeKind.Copied => false,
            _ => throw new InvalidOperationException($"unsupported raw change kind: {change.Kind}"),
        }).ToArray();
        if (endpoints.Length == 0)
        {
            return Admissible(AdmissionPlaneClassification.Empty);
        }

        var fileMap = candidate.Entries.FirstOrDefault(
            static entry => entry.Path == FileMapPath);
        if (fileMap is null)
        {
            return Failed(
                "ADMISSION-PLANE-FILEMAP-UNAVAILABLE",
                FileMapPath,
                "candidate FILEMAP is unavailable");
        }

        // Historical registration applies only when the immutable snapshots confirm
        // that an endpoint existed in the base and is absent from the candidate.
        var candidatePaths = candidate.Entries
            .Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        var protectedBasePaths = protectedBase.Entries
            .Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        var deletedPaths = endpoints
            .Select(static change => change.Path.Value)
            .Where(path => !candidatePaths.Contains(path) && protectedBasePaths.Contains(path))
            .ToHashSet(StringComparer.Ordinal);

        AdmissionPlaneFileMap candidateManifest;
        AdmissionPlaneFileMap? baseManifest = null;
        var source = "candidate FILEMAP";
        try
        {
            candidateManifest = AdmissionPlaneFileMapLoader.Parse(
                fileMap.Bytes.AsSpan(),
                FileMapPath,
                path => ReadInclude(candidate, path));
            if (deletedPaths.Count > 0)
            {
                source = "protected-base FILEMAP";
                var baseFileMap = protectedBase.Entries.FirstOrDefault(
                    static entry => entry.Path == FileMapPath);
                if (baseFileMap is null)
                {
                    return Failed(
                        "ADMISSION-PLANE-FILEMAP-UNAVAILABLE",
                        FileMapPath,
                        "protected-base FILEMAP is unavailable");
                }

                baseManifest = AdmissionPlaneFileMapLoader.Parse(
                    baseFileMap.Bytes.AsSpan(),
                    $"protected-base {FileMapPath}",
                    path => ReadInclude(protectedBase, path));
            }
        }
        catch (FileMapParseException exception)
        {
            return Failed(
                "ADMISSION-PLANE-FILEMAP-INVALID",
                FileMapPath,
                $"{source} cannot be parsed: {exception.Message}");
        }
        catch (FileMapPatternException exception)
        {
            return Failed(
                FileMapPatternException.FindingCode,
                exception.Pattern,
                $"{source}: {FileMapPatternException.FindingCode}: {exception.Message}");
        }
        catch (FormatException exception)
        {
            return Failed(
                "ADMISSION-PLANE-FILEMAP-INVALID",
                FileMapPath,
                $"{source}: {exception.Message}");
        }

        var judgePaths = new List<string>();
        var contentPaths = new List<string>();
        foreach (var change in endpoints)
        {
            var path = change.Path.Value;
            var deleted = deletedPaths.Contains(path);
            var manifest = deleted ? baseManifest! : candidateManifest;
            var matches = manifest.Match(path);
            if (matches is not [var match])
            {
                return Failed(
                    "ADMISSION-PLANE-PATH-MATCH-COUNT",
                    path,
                    "changed path must match exactly one FILEMAP entry; "
                    + $"path={path} matches={matches.Length} "
                    + $"manifest={(deleted ? "protected-base" : "candidate")}");
            }

            if (FileMapDocuments.IsPolicyPath(path) && match.AdmissionPlane is not FileMapAdmissionPlane.Judge)
                return Failed("FILEMAP-ADMISSION-PLANE-INVALID", path,
                    "FILEMAP policy source must be assigned to the judge admission plane");

            if (match.AdmissionPlane is FileMapAdmissionPlane.Judge)
            {
                judgePaths.Add(path);
            }
            else
            {
                contentPaths.Add(path);
            }
        }

        if (judgePaths.Count > 0 && contentPaths.Count > 0)
        {
            return new AdmissionPlaneDecision(
                false,
                AdmissionPlaneClassification.Mixed,
                MixedCode,
                FileMapPath,
                "judge and content paths cannot be submitted together");
        }

        return Admissible(
            judgePaths.Count > 0
                ? AdmissionPlaneClassification.JudgeOnly
                : AdmissionPlaneClassification.ContentOnly);
    }

    internal static AdmissionPlaneDecision Evaluate(
        ReadOnlySpan<byte> candidateFileMap,
        IReadOnlyList<string> changedPaths)
    {
        ArgumentNullException.ThrowIfNull(changedPaths);
        var candidate = RawRepositorySnapshot.Create(
            [new RawRepositoryEntry(FileMapPath, ImmutableArray.Create(candidateFileMap.ToArray()))]);
        return Evaluate(candidate, candidate, RawChangeSet.Create(changedPaths));
    }

    private static byte[] ReadInclude(RawRepositorySnapshot snapshot, string path) =>
        snapshot.Entries.FirstOrDefault(entry => entry.Path == path)?.Bytes.ToArray()
        ?? throw new FileMapParseException(path, "included file is unavailable in this snapshot");

    private static AdmissionPlaneDecision Admissible(
        AdmissionPlaneClassification classification) =>
        new(true, classification, string.Empty, string.Empty, string.Empty);

    private static AdmissionPlaneDecision Failed(
        string code,
        string path,
        string message) =>
        new(false, null, code, path, message);
}

internal sealed class AdmissionPlaneFileMapEntry
{
    private readonly FileMapGlob glob;

    internal AdmissionPlaneFileMapEntry(string pattern, FileMapAdmissionPlane admissionPlane)
    {
        glob = FileMapGlob.CreateForAdmissionPlane(pattern);
        Pattern = pattern;
        AdmissionPlane = admissionPlane;
    }

    internal string Pattern { get; }

    internal FileMapAdmissionPlane AdmissionPlane { get; }

    internal bool Matches(string path) => glob.IsMatch(path);
}

internal sealed class AdmissionPlaneFileMap
{
    internal AdmissionPlaneFileMap(ImmutableArray<AdmissionPlaneFileMapEntry> entries) =>
        Entries = entries;

    internal ImmutableArray<AdmissionPlaneFileMapEntry> Entries { get; }

    internal ImmutableArray<AdmissionPlaneFileMapEntry> Match(string path) =>
        Entries.Where(entry => entry.Matches(path)).ToImmutableArray();
}

internal static class AdmissionPlaneFileMapLoader
{
    internal static AdmissionPlaneFileMap Parse(
        ReadOnlySpan<byte> bytes,
        string location,
        Func<string, byte[]>? readInclude = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(location);
        var documents = FileMapDocuments.Resolve(bytes, location, readInclude);
        var entries = ImmutableArray.CreateBuilder<AdmissionPlaneFileMapEntry>();
        foreach (var document in documents)
        {
            if (!document.Table.TryGetValue("files", out var rawFiles)) continue;
            var files = FileMapTomlTables.Parse(rawFiles, document.Path, allowEmpty: true);
            entries.AddRange(files.Select((table, index) => ParseEntry(table, $"{document.Path}:files[{index}]")));
        }

        return new AdmissionPlaneFileMap(entries.ToImmutable());
    }

    private static AdmissionPlaneFileMapEntry ParseEntry(TomlTable table, string location)
    {
        if (!table.TryGetValue("pattern", out var rawPattern) || rawPattern is not string pattern)
        {
            throw Invalid(location, "pattern must be a string");
        }

        if (!table.ContainsKey("admission_plane"))
        {
            throw new FileMapAdmissionPlaneException(
                "FILEMAP-ADMISSION-PLANE-MISSING",
                pattern,
                location,
                "admission_plane is required");
        }

        table.TryGetValue("admission_plane", out var rawPlane);
        var admissionPlane = rawPlane switch
        {
            "judge" => FileMapAdmissionPlane.Judge,
            "content" => FileMapAdmissionPlane.Content,
            _ => throw new FileMapAdmissionPlaneException(
                "FILEMAP-ADMISSION-PLANE-INVALID",
                pattern,
                location,
                "admission_plane must be judge or content"),
        };
        return new AdmissionPlaneFileMapEntry(pattern, admissionPlane);
    }

    private static FormatException Invalid(string location, string message) =>
        new($"Invalid FILEMAP at {location}: {message}.");
}
