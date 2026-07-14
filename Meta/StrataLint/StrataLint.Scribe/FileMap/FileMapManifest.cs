using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Scribe;

internal enum FileMapKind
{
    Truth,
    Program,
    Data,
    Generated,
    Ledger,
}

internal sealed record FileMapEntry
{
    private readonly FileMapGlob glob;

    internal FileMapEntry(
        string pattern,
        FileMapKind kind,
        string producedBy,
        ImmutableArray<string> consumedBy,
        ImmutableArray<string> verifiedBy)
    {
        glob = FileMapGlob.Create(pattern);
        Pattern = pattern;
        Kind = kind;
        ProducedBy = producedBy;
        ConsumedBy = consumedBy;
        VerifiedBy = verifiedBy;
    }

    internal string Pattern { get; }

    internal FileMapKind Kind { get; }

    internal string ProducedBy { get; }

    internal ImmutableArray<string> ConsumedBy { get; }

    internal ImmutableArray<string> VerifiedBy { get; }

    internal bool Matches(string path) => glob.IsMatch(path);
}

internal sealed class FileMapManifest
{
    internal FileMapManifest(ImmutableArray<FileMapEntry> entries) => Entries = entries;

    internal ImmutableArray<FileMapEntry> Entries { get; }

    internal ImmutableArray<FileMapEntry> Match(string path) =>
        Entries.Where(entry => entry.Matches(path)).ToImmutableArray();
}

internal static class FileMapLoader
{
    internal const string RelativePath = "Meta/FILEMAP.toml";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly Regex NamePattern = new(
        "^[A-Za-z][A-Za-z0-9.-]*$",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    private static readonly string[] EntryKeys =
        ["consumed_by", "kind", "pattern", "produced_by", "verified_by"];

    internal static FileMapManifest LoadRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var path = Path.Combine(repositoryRoot, RelativePath);
        return Parse(File.ReadAllBytes(path), path);
    }

    internal static FileMapManifest Parse(ReadOnlySpan<byte> bytes, string location)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(location);
        if (bytes.IsEmpty
            || bytes[^1] != (byte)'\n'
            || bytes.Contains((byte)'\r')
            || bytes.Length >= 3
                && bytes[0] == 0xEF
                && bytes[1] == 0xBB
                && bytes[2] == 0xBF)
        {
            throw Invalid(location, "bytes must be strict UTF-8 without BOM/CR and end in LF");
        }

        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw Invalid(location, "bytes are not strict UTF-8", exception);
        }

        TomlTable root;
        try
        {
            root = TomlSerializer.Deserialize<TomlTable>(text)
                ?? throw Invalid(location, "TOML decoded to null");
        }
        catch (TomlException exception)
        {
            throw Invalid(location, $"invalid TOML: {exception.Message}", exception);
        }

        RequireExactKeys(root, location, "files", "schema_version");
        if (root["schema_version"] is not long schemaVersion || schemaVersion != 1)
        {
            throw Invalid(location, "schema_version must be 1");
        }

        if (root["files"] is not TomlTableArray files || files.Count == 0)
        {
            throw Invalid(location, "files must contain at least one entry");
        }

        var entries = files
            .Select((table, index) => ParseEntry(table, $"{location}:files[{index}]") )
            .ToImmutableArray();
        var patterns = entries.Select(static entry => entry.Pattern).ToArray();
        if (!patterns.SequenceEqual(patterns.Order(StringComparer.Ordinal), StringComparer.Ordinal)
            || patterns.Distinct(StringComparer.Ordinal).Count() != patterns.Length)
        {
            throw Invalid(location, "file patterns must be unique and ordinally sorted");
        }

        return new FileMapManifest(entries);
    }

    private static FileMapEntry ParseEntry(TomlTable table, string location)
    {
        RequireExactKeys(table, location, EntryKeys);
        var pattern = RequiredString(table, "pattern", location);
        _ = FileMapGlob.Create(pattern);
        var kind = RequiredString(table, "kind", location) switch
        {
            "truth" => FileMapKind.Truth,
            "program" => FileMapKind.Program,
            "data" => FileMapKind.Data,
            "generated" => FileMapKind.Generated,
            "ledger" => FileMapKind.Ledger,
            _ => throw Invalid(location, "kind must be truth, program, data, generated, or ledger"),
        };
        var producedBy = RequiredName(table, "produced_by", location, allowNone: true);
        var consumedBy = RequiredNames(table, "consumed_by", location);
        var verifiedBy = RequiredNames(table, "verified_by", location);
        if (kind is FileMapKind.Generated
            && (producedBy == "none" || !verifiedBy.Contains("emit-check", StringComparer.Ordinal)))
        {
            throw Invalid(
                location,
                producedBy == "none"
                    ? "generated produced_by must name a producer"
                    : "generated verified_by must include emit-check");
        }

        return new FileMapEntry(pattern, kind, producedBy, consumedBy, verifiedBy);
    }

    private static ImmutableArray<string> RequiredNames(
        TomlTable table,
        string key,
        string location)
    {
        if (!table.TryGetValue(key, out var raw) || raw is not TomlArray array || array.Count == 0)
        {
            throw Invalid(location, $"{key} must be a non-empty string array");
        }

        var values = array.Select((value, index) => value is string text
                ? ValidateName(text, $"{location}:{key}[{index}]", allowNone: false)
                : throw Invalid(location, $"{key} must contain only strings"))
            .ToImmutableArray();
        if (!values.SequenceEqual(values.Order(StringComparer.Ordinal), StringComparer.Ordinal)
            || values.Distinct(StringComparer.Ordinal).Count() != values.Length)
        {
            throw Invalid(location, $"{key} must be unique and ordinally sorted");
        }

        return values;
    }

    private static string RequiredName(
        TomlTable table,
        string key,
        string location,
        bool allowNone) =>
        ValidateName(RequiredString(table, key, location), $"{location}:{key}", allowNone);

    private static string ValidateName(string value, string location, bool allowNone) =>
        allowNone && value == "none" || NamePattern.IsMatch(value)
            ? value
            : throw Invalid(location, "value is not a canonical program/check name");

    private static string RequiredString(TomlTable table, string key, string location) =>
        table.TryGetValue(key, out var raw)
        && raw is string value
        && !string.IsNullOrWhiteSpace(value)
        && string.Equals(value, value.Trim(), StringComparison.Ordinal)
            ? value
            : throw Invalid(location, $"{key} must be a non-empty canonical string");

    private static void RequireExactKeys(TomlTable table, string location, params string[] expected)
    {
        var expectedSet = expected.ToHashSet(StringComparer.Ordinal);
        var unknown = table.Keys.Where(key => !expectedSet.Contains(key)).Order(StringComparer.Ordinal).ToArray();
        var missing = expectedSet.Where(key => !table.ContainsKey(key)).Order(StringComparer.Ordinal).ToArray();
        if (unknown.Length != 0 || missing.Length != 0)
        {
            throw Invalid(
                location,
                $"unknown keys [{string.Join(", ", unknown)}] or missing keys [{string.Join(", ", missing)}]");
        }
    }

    private static FormatException Invalid(string location, string message, Exception? inner = null) =>
        new($"Invalid FILEMAP at {location}: {message}.", inner);
}
