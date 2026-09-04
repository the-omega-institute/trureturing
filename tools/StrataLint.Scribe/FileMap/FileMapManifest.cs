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

internal enum FileMapAdmissionPlane
{
    Judge,
    Content,
}

internal sealed record FileMapResidencePolicy(
    string CaseId,
    string Desired,
    int KnownViolationCount,
    string Status);

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

internal sealed record FileMapEntry
{
    private readonly FileMapGlob glob;

    internal FileMapEntry(
        string pattern,
        FileMapKind kind,
        FileMapAdmissionPlane admissionPlane,
        string producedBy,
        ImmutableArray<string> consumedBy,
        ImmutableArray<string> verifiedBy,
        bool residenceViolation,
        string artifactId,
        string? mode,
        string runtimeDisposition,
        string? historyRequirement)
    {
        glob = FileMapGlob.Create(pattern);
        Pattern = pattern;
        Kind = kind;
        AdmissionPlane = admissionPlane;
        ProducedBy = producedBy;
        ConsumedBy = consumedBy;
        VerifiedBy = verifiedBy;
        ResidenceViolation = residenceViolation;
        ArtifactId = artifactId;
        Mode = mode;
        RuntimeDisposition = runtimeDisposition;
        HistoryRequirement = historyRequirement;
    }

    internal string Pattern { get; }

    internal FileMapKind Kind { get; }

    internal FileMapAdmissionPlane AdmissionPlane { get; }

    internal string ProducedBy { get; }

    internal ImmutableArray<string> ConsumedBy { get; }

    internal ImmutableArray<string> VerifiedBy { get; }

    internal bool ResidenceViolation { get; }

    internal string ArtifactId { get; }

    internal string? Mode { get; }

    internal string RuntimeDisposition { get; }

    internal string? HistoryRequirement { get; }

    internal bool Matches(string path) => glob.IsMatch(path);
}

internal sealed class FileMapManifest
{
    internal FileMapManifest(
        FileMapResidencePolicy residencePolicy,
        ImmutableArray<FileMapEntry> entries)
    {
        ResidencePolicy = residencePolicy;
        Entries = entries;
    }

    internal FileMapResidencePolicy ResidencePolicy { get; }

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
        ["admission_plane", "artifact_id", "consumed_by", "kind", "pattern", "produced_by", "runtime_disposition", "verified_by"];
    private static readonly string[] ResidenceEntryKeys =
        ["admission_plane", "artifact_id", "consumed_by", "kind", "pattern", "produced_by", "residence_violation", "runtime_disposition", "verified_by"];
    private static readonly string[] RunLocalEntryKeys =
        ["admission_plane", "artifact_id", "consumed_by", "history_requirement", "kind", "mode", "pattern", "produced_by", "runtime_disposition", "verified_by"];
    private static readonly string[] GeneratedArtifactEntryKeys = RunLocalEntryKeys;

    internal static FileMapManifest LoadRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var path = Path.Combine(repositoryRoot, RelativePath);
        return Parse(File.ReadAllBytes(path), path);
    }

    internal static FileMapManifest Parse(ReadOnlySpan<byte> bytes, string location)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(location);
        if (bytes.Length >= 3
            && bytes[0] == 0xEF
            && bytes[1] == 0xBB
            && bytes[2] == 0xBF)
        {
            throw new FileMapParseException(location, "bytes contain a UTF-8 BOM");
        }

        if (bytes.IsEmpty || bytes[^1] != (byte)'\n' || bytes.Contains((byte)'\r'))
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

        RequireExactKeys(root, location, "files", "residence_policy", "schema_version");
        if (root["schema_version"] is not long schemaVersion || schemaVersion != 2)
        {
            throw Invalid(location, "schema_version must be 2");
        }

        if (root["files"] is not TomlTableArray files || files.Count == 0)
        {
            throw Invalid(location, "files must contain at least one entry");
        }

        if (root["residence_policy"] is not TomlTable residenceTable)
        {
            throw Invalid(location, "residence_policy must be a table");
        }

        var residencePolicy = ParseResidencePolicy(
            residenceTable,
            $"{location}:residence_policy");

        var entries = files
            .Select((table, index) => ParseEntry(table, $"{location}:files[{index}]") )
            .ToImmutableArray();
        var patterns = entries.Select(static entry => entry.Pattern).ToArray();
        if (!patterns.SequenceEqual(patterns.Order(StringComparer.Ordinal), StringComparer.Ordinal)
            || patterns.Distinct(StringComparer.Ordinal).Count() != patterns.Length)
        {
            throw Invalid(location, "file patterns must be unique and ordinally sorted");
        }

        var artifactIds = entries
            .Where(static entry => entry.ArtifactId != "none")
            .Select(static entry => entry.ArtifactId)
            .ToArray();
        if (artifactIds.Distinct(StringComparer.Ordinal).Count() != artifactIds.Length)
        {
            throw Invalid(location, "artifact_id values other than none must be unique");
        }

        return new FileMapManifest(residencePolicy, entries);
    }

    private static FileMapResidencePolicy ParseResidencePolicy(
        TomlTable table,
        string location)
    {
        RequireExactKeys(
            table,
            location,
            "case_id",
            "desired",
            "known_violation_count",
            "status");
        var count = table["known_violation_count"] is long rawCount
            && rawCount >= 0
            && rawCount <= int.MaxValue
                ? (int)rawCount
                : throw Invalid(location, "known_violation_count must be a non-negative 32-bit integer");
        return new FileMapResidencePolicy(
            RequiredName(table, "case_id", location, allowNone: false),
            RequiredString(table, "desired", location),
            count,
            RequiredString(table, "status", location));
    }

    private static FileMapEntry ParseEntry(TomlTable table, string location)
    {
        if (!table.ContainsKey("admission_plane"))
        {
            var path = table.TryGetValue("pattern", out var rawPattern)
                && rawPattern is string declaredPattern
                    ? declaredPattern
                    : location;
            throw new FileMapAdmissionPlaneException(
                "FILEMAP-ADMISSION-PLANE-MISSING",
                path,
                location,
                "admission_plane is required");
        }

        var hasResidenceViolation = table.ContainsKey("residence_violation");
        var isRunLocal = table.TryGetValue("runtime_disposition", out var disposition)
            && disposition is "run-local";
        var isDataKeyedGeneratedSet = table.TryGetValue("kind", out var dataKeyedKind)
            && dataKeyedKind is "generated"
            && table.TryGetValue("artifact_id", out var dataKeyedArtifactId)
            && dataKeyedArtifactId is "none"
            && table.TryGetValue("pattern", out var dataKeyedPattern)
            && dataKeyedPattern is string patternValue
            && patternValue.Contains('*');
        var isDataKeyedRunLocal = isRunLocal && isDataKeyedGeneratedSet;
        var isGeneratedArtifact = table.TryGetValue("kind", out var rawKind)
            && rawKind is "generated"
            && table.TryGetValue("artifact_id", out var rawArtifactId)
            && rawArtifactId is string artifactIdValue
            && artifactIdValue != "none"
            && disposition is "committed-source";
        RequireExactKeys(table, location, isDataKeyedRunLocal ? EntryKeys : isRunLocal ? RunLocalEntryKeys : isGeneratedArtifact ? GeneratedArtifactEntryKeys : hasResidenceViolation ? ResidenceEntryKeys : EntryKeys);
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
        var admissionPlane = RequiredAdmissionPlane(table, pattern, location);
        var producedBy = RequiredName(table, "produced_by", location, allowNone: true);
        var consumedBy = RequiredNames(table, "consumed_by", location);
        var verifiedBy = RequiredNames(table, "verified_by", location);
        var residenceViolation = !hasResidenceViolation
            ? false
            : table["residence_violation"] is true
                ? true
                : throw Invalid(location, "residence_violation must be the canonical boolean true");
        if (residenceViolation && kind is not FileMapKind.Data)
        {
            throw Invalid(location, "residence_violation is valid only for data entries");
        }

        if (kind is FileMapKind.Generated
            && (producedBy == "none" || !verifiedBy.Contains(producedBy, StringComparer.Ordinal)))
        {
            throw Invalid(
                location,
                producedBy == "none"
                    ? "generated produced_by must name a producer"
                    : "generated verified_by must include its producer");
        }

        var artifactId = RequiredName(table, "artifact_id", location, allowNone: true);
        var runtimeDisposition = RequiredString(table, "runtime_disposition", location);
        _ = runtimeDisposition switch
        {
            "committed-source" => runtimeDisposition,
            "committed-ledger" => runtimeDisposition,
            "run-local" => runtimeDisposition,
            _ => throw Invalid(location, "runtime_disposition must be committed-source, committed-ledger, or run-local"),
        };
        var hasProjectionFields = (isRunLocal && !isDataKeyedGeneratedSet) || isGeneratedArtifact;
        var mode = hasProjectionFields ? RequiredString(table, "mode", location) : null;
        var historyRequirement = hasProjectionFields ? RequiredString(table, "history_requirement", location) : null;
        if (hasProjectionFields
            && (kind is not FileMapKind.Generated || artifactId == "none"
                || mode is null || mode.Length != 6 || mode.Any(static value => value is < '0' or > '7')
                || historyRequirement != "not-required"))
        {
            throw Invalid(location, "generated artifact projection fields are invalid");
        }
        if (runtimeDisposition == "committed-ledger"
            && kind is not FileMapKind.Ledger)
        {
            throw Invalid(location, "committed-ledger disposition requires ledger kind");
        }
        if (kind is FileMapKind.Ledger
            && runtimeDisposition != "committed-ledger")
        {
            throw Invalid(location, "ledger kind requires committed-ledger disposition");
        }

        return new FileMapEntry(
            pattern,
            kind,
            admissionPlane,
            producedBy,
            consumedBy,
            verifiedBy,
            residenceViolation,
            artifactId,
            mode,
            runtimeDisposition,
            historyRequirement);
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

    private static FileMapAdmissionPlane RequiredAdmissionPlane(
        TomlTable table,
        string pattern,
        string location)
    {
        table.TryGetValue("admission_plane", out var raw);
        var value = raw as string;
        if (value != "judge" && value != "content")
        {
            throw InvalidAdmissionPlane(pattern, location);
        }

        return value == "judge"
            ? FileMapAdmissionPlane.Judge
            : FileMapAdmissionPlane.Content;
    }

    private static FileMapAdmissionPlaneException InvalidAdmissionPlane(
        string pattern,
        string location) =>
        new(
            "FILEMAP-ADMISSION-PLANE-INVALID",
            pattern,
            location,
            "admission_plane must be judge or content");

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
