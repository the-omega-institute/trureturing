using System.Collections.Immutable;
using System.Text;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Scribe;

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

        if (rawFiles is not TomlTableArray files)
        {
            throw Invalid(location, "files must be an array of tables");
        }

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
