using System.Collections.Immutable;
using System.Text;
using Tomlyn;
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

internal enum AdmissionPlaneClassification
{
    Empty,
    JudgeOnly,
    ContentOnly,
    Bootstrap,
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

        return Classification is AdmissionPlaneClassification.JudgeOnly
            or AdmissionPlaneClassification.Bootstrap;
    }
}

internal static class AdmissionPlanePolicy
{
    internal const string FileMapPath = "Meta/FILEMAP.toml";
    internal const string MixedCode = "ADMISSION-PLANE-MIXED";

    private const string CiPath = ".github/workflows/ci.yml";
    private static readonly string[] RepairPaths = [CiPath, FileMapPath];

    internal static AdmissionPlaneDecision Evaluate(
        RawRepositorySnapshot protectedBase,
        IReadOnlyList<string> changedPaths)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(changedPaths);
        if (changedPaths.Count == 0)
        {
            return Admissible(AdmissionPlaneClassification.Empty);
        }

        var fileMap = protectedBase.Entries.FirstOrDefault(
            static entry => entry.Path == FileMapPath);
        return fileMap is null
            ? EvaluateUnavailable(changedPaths)
            : Evaluate(fileMap.Bytes.AsSpan(), changedPaths);
    }

    internal static AdmissionPlaneDecision Evaluate(
        ReadOnlySpan<byte> protectedBaseFileMap,
        IReadOnlyList<string> changedPaths)
    {
        ArgumentNullException.ThrowIfNull(changedPaths);
        if (changedPaths.Count == 0)
        {
            return Admissible(AdmissionPlaneClassification.Empty);
        }

        var isRepair = IsRepair(changedPaths);
        AdmissionPlaneFileMap manifest;
        try
        {
            manifest = AdmissionPlaneFileMapLoader.Parse(
                protectedBaseFileMap,
                $"protected-base:{FileMapPath}");
        }
        catch (FileMapParseException exception)
        {
            return isRepair
                ? Admissible(AdmissionPlaneClassification.Bootstrap)
                : Failed(
                    "ADMISSION-PLANE-BASE-FILEMAP-INVALID",
                    FileMapPath,
                    $"protected-base FILEMAP cannot be parsed: {exception.Message}");
        }
        catch (FileMapPatternException exception)
        {
            return Failed(
                FileMapPatternException.FindingCode,
                exception.Pattern,
                $"{FileMapPatternException.FindingCode}: {exception.Message}");
        }
        catch (FormatException exception)
        {
            return Failed(
                "ADMISSION-PLANE-BASE-FILEMAP-INVALID",
                FileMapPath,
                exception.Message);
        }

        var judgePaths = new List<string>();
        var contentPaths = new List<string>();
        foreach (var path in changedPaths)
        {
            var matches = manifest.Match(path);
            if (matches is not [var match])
            {
                return Failed(
                    "ADMISSION-PLANE-PATH-MATCH-COUNT",
                    path,
                    "changed path must match exactly one protected-base FILEMAP entry; "
                    + $"path={path} matches={matches.Length}");
            }

            if (match.AdmissionPlane is FileMapAdmissionPlane.Judge)
            {
                judgePaths.Add(path);
            }
            else
            {
                contentPaths.Add(path);
            }
        }

        if (isRepair)
        {
            var invalid = RepairPaths.FirstOrDefault(path =>
                manifest.Match(path) is not [{ AdmissionPlane: FileMapAdmissionPlane.Judge }]);
            if (invalid is not null)
            {
                return Failed(
                    "ADMISSION-PLANE-REPAIR-PATH-NOT-JUDGE",
                    invalid,
                    $"reserved repair path must resolve once to judge: {invalid}");
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

    private static AdmissionPlaneDecision EvaluateUnavailable(IReadOnlyList<string> changedPaths) =>
        IsRepair(changedPaths)
            ? Admissible(AdmissionPlaneClassification.Bootstrap)
            : Failed(
                "ADMISSION-PLANE-BASE-FILEMAP-UNAVAILABLE",
                FileMapPath,
                "protected-base FILEMAP is unavailable outside the repair boundary");

    private static bool IsRepair(IReadOnlyList<string> changedPaths) =>
        changedPaths.All(path => RepairPaths.Contains(path, StringComparer.Ordinal));

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
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static AdmissionPlaneFileMap Parse(ReadOnlySpan<byte> bytes, string location)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(location);
        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FileMapParseException(location, "bytes are not strict UTF-8", exception);
        }

        TomlTable root;
        try
        {
            root = TomlSerializer.Deserialize<TomlTable>(text)
                ?? throw Invalid(location, "TOML decoded to null");
        }
        catch (TomlException exception)
        {
            throw new FileMapParseException(location, $"invalid TOML: {exception.Message}", exception);
        }

        if (!root.TryGetValue("files", out var rawFiles))
        {
            return new AdmissionPlaneFileMap([]);
        }

        var files = rawFiles switch
        {
            TomlTableArray tables => tables.Cast<TomlTable>().ToArray(),
            TomlArray values when values.All(static value => value is TomlTable) =>
                values.Cast<TomlTable>().ToArray(),
            _ => throw Invalid(location, "files must be an array of tables"),
        };
        return new AdmissionPlaneFileMap(files
            .Select((table, index) => ParseEntry(table, $"{location}:files[{index}]"))
            .ToImmutableArray());
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
