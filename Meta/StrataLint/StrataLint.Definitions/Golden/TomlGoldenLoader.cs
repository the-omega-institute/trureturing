using System.Text;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Definitions;

internal static class TomlGoldenLoader
{
    internal const string RelativeDirectory = "Meta/StrataLint/Golden/cases";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static GoldenCorpusSet LoadRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        return LoadDirectory(Path.Combine(repositoryRoot, RelativeDirectory));
    }

    internal static GoldenCorpusSet LoadDirectory(string directory)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(directory);
        var fullDirectory = Path.GetFullPath(directory);
        if (!Directory.Exists(fullDirectory))
        {
            throw new DirectoryNotFoundException($"golden corpus directory is absent: {fullDirectory}");
        }

        var entries = Directory.EnumerateFileSystemEntries(fullDirectory)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (entries.Length == 0)
        {
            throw new FormatException($"golden corpus directory is empty: {fullDirectory}");
        }

        foreach (var entry in entries)
        {
            if (!File.Exists(entry)
                || !string.Equals(Path.GetExtension(entry), ".toml", StringComparison.Ordinal))
            {
                throw new FormatException($"golden corpus contains a non-TOML entry: {entry}");
            }
        }

        var files = entries.Select(LoadFile).ToArray();
        var names = new HashSet<string>(StringComparer.Ordinal);
        foreach (var testCase in files.SelectMany(static file => file.Cases))
        {
            if (!names.Add(testCase.Name))
            {
                throw new FormatException($"duplicate golden case name: {testCase.Name}");
            }
        }

        return new GoldenCorpusSet(files);
    }

    internal static GoldenCorpusFile LoadFile(string path)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(path);
        var fullPath = Path.GetFullPath(path);
        var bytes = File.ReadAllBytes(fullPath);
        if (bytes.Length >= 3
            && bytes[0] == 0xEF
            && bytes[1] == 0xBB
            && bytes[2] == 0xBF)
        {
            throw Invalid(fullPath, "UTF-8 BOM is forbidden");
        }

        if (bytes.AsSpan().Contains((byte)'\r'))
        {
            throw Invalid(fullPath, "CR bytes are forbidden; use LF");
        }

        if (bytes.Length == 0 || bytes[^1] != (byte)'\n')
        {
            throw Invalid(fullPath, "file must end with exactly one LF");
        }

        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw Invalid(fullPath, "file must be strict UTF-8", exception);
        }

        TomlTable root;
        try
        {
            root = TomlSerializer.Deserialize<TomlTable>(text)
                ?? throw Invalid(fullPath, "TOML document decoded to null");
        }
        catch (TomlException exception)
        {
            throw Invalid(fullPath, $"invalid TOML: {exception.Message}", exception);
        }

        RequireKeys(root, fullPath, "cases");
        if (root["cases"] is not TomlTableArray cases || cases.Count == 0)
        {
            throw Invalid(fullPath, "key 'cases' must be a non-empty table array");
        }

        var parsed = new GoldenCase[cases.Count];
        var names = new HashSet<string>(StringComparer.Ordinal);
        for (var index = 0; index < cases.Count; index++)
        {
            parsed[index] = ParseCase(cases[index], $"{fullPath}:cases[{index}]");
            if (!names.Add(parsed[index].Name))
            {
                throw Invalid(fullPath, $"duplicate golden case name: {parsed[index].Name}");
            }
        }

        var result = new GoldenCorpusFile(fullPath, parsed);
        var canonical = TomlGoldenWriter.Write(result.Cases);
        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            throw Invalid(fullPath, "bytes are not canonical golden TOML");
        }

        return result;
    }

    private static GoldenCase ParseCase(TomlTable table, string location)
    {
        RequireKeys(
            table,
            location,
            "name",
            "changes",
            "baseline_mutations",
            "mutations",
            "expected_diagnostics");
        var name = RequiredString(table, "name", location);
        if (string.IsNullOrWhiteSpace(name))
        {
            throw Invalid(location, "key 'name' must not be empty");
        }

        return new GoldenCase(
            name,
            ParseMutations(RequiredArray(table, "baseline_mutations", location), location, "baseline_mutations"),
            ParseMutations(RequiredArray(table, "mutations", location), location, "mutations"),
            ParseDiagnostics(RequiredArray(table, "expected_diagnostics", location), location),
            RequiredStringArray(table, "changes", location));
    }

    private static GoldenMutation[] ParseMutations(
        TomlArray values,
        string location,
        string key)
    {
        var result = new GoldenMutation[values.Count];
        for (var index = 0; index < values.Count; index++)
        {
            if (values[index] is not TomlTable table)
            {
                throw Invalid(location, $"key '{key}[{index}]' must be an inline table");
            }

            result[index] = ParseMutation(table, $"{location}.{key}[{index}]");
        }

        return result;
    }

    private static GoldenMutation ParseMutation(TomlTable table, string location)
    {
        var op = RequiredString(table, "op", location);
        switch (op)
        {
            case "write":
                RequireKeys(table, location, "op", "path", "content");
                return new GoldenMutation.Write(
                    RequiredString(table, "path", location),
                    RequiredString(table, "content", location));
            case "write_parts":
                RequireKeys(table, location, "op", "path", "parts");
                return new GoldenMutation.WriteParts(
                    RequiredString(table, "path", location),
                    RequiredStringArray(table, "parts", location));
            case "lean":
                RequireKeys(table, location, "op", "path", "raw_gid", "generality", "body");
                return new GoldenMutation.Lean(
                    RequiredString(table, "path", location),
                    RequiredString(table, "raw_gid", location),
                    RequiredGenerality(table, "generality", location),
                    RequiredString(table, "body", location));
            case "delete":
                RequireKeys(table, location, "op", "path");
                return new GoldenMutation.Delete(RequiredString(table, "path", location));
            case "append_lines":
                RequireKeys(table, location, "op", "path", "count", "line");
                return new GoldenMutation.AppendLines(
                    RequiredString(table, "path", location),
                    RequiredInt32(table, "count", location, minimum: 0),
                    RequiredString(table, "line", location));
            case "add_domain":
                RequireKeys(table, location, "op", "name", "stratum");
                return new GoldenMutation.AddDomain(
                    RequiredString(table, "name", location),
                    RequiredStratum(table, "stratum", location));
            case "add_task":
                RequireKeys(table, location, "op", "path", "raw_gid", "raw_case_id");
                return new GoldenMutation.AddTask(
                    RequiredString(table, "path", location),
                    RequiredString(table, "raw_gid", location),
                    RequiredString(table, "raw_case_id", location));
            case "populate_directory":
                RequireKeys(table, location, "op");
                return new GoldenMutation.PopulateDirectory();
            case "empty_mirror_waiver":
                RequireKeys(table, location, "op");
                return new GoldenMutation.EmptyMirrorWaiver();
            case "evidence_mirror":
                RequireKeys(table, location, "op", "include_json", "include_yaml");
                return new GoldenMutation.EvidenceMirror(
                    RequiredBoolean(table, "include_json", location),
                    RequiredBoolean(table, "include_yaml", location));
            case "replace_backfill":
                RequireKeys(table, location, "op", "old_value", "new_value");
                return new GoldenMutation.ReplaceBackfill(
                    RequiredString(table, "old_value", location),
                    RequiredString(table, "new_value", location));
            case "replace_first_backfill_disposition":
                RequireKeys(table, location, "op", "raw_gid");
                return new GoldenMutation.ReplaceFirstBackfillDisposition(
                    RequiredString(table, "raw_gid", location));
            case "mutate_backfill_anchor":
                RequireKeys(table, location, "op", "anchor", "duplicate");
                return new GoldenMutation.MutateBackfillAnchor(
                    RequiredString(table, "anchor", location),
                    RequiredBoolean(table, "duplicate", location));
            default:
                throw Invalid(location, $"unknown golden mutation op '{op}'");
        }
    }

    private static GoldenDiagnostic[] ParseDiagnostics(TomlArray values, string location)
    {
        var result = new GoldenDiagnostic[values.Count];
        for (var index = 0; index < values.Count; index++)
        {
            var diagnosticLocation = $"{location}.expected_diagnostics[{index}]";
            if (values[index] is not TomlTable table)
            {
                throw Invalid(location, $"key 'expected_diagnostics[{index}]' must be an inline table");
            }

            RequireKeys(table, diagnosticLocation, "rule", "path", "message");
            result[index] = new GoldenDiagnostic(
                RequiredInt32(table, "rule", diagnosticLocation, minimum: 0),
                RequiredString(table, "path", diagnosticLocation),
                RequiredString(table, "message", diagnosticLocation));
        }

        return result;
    }

    private static void RequireKeys(TomlTable table, string location, params string[] required)
    {
        var allowed = required.ToHashSet(StringComparer.Ordinal);
        foreach (var key in table.Keys)
        {
            if (!allowed.Contains(key))
            {
                throw Invalid(location, $"unknown key '{key}'");
            }
        }

        foreach (var key in required)
        {
            if (!table.ContainsKey(key))
            {
                throw Invalid(location, $"missing required key '{key}'");
            }
        }
    }

    private static TomlArray RequiredArray(TomlTable table, string key, string location) =>
        table.TryGetValue(key, out var value) && value is TomlArray array
            ? array
            : throw Invalid(location, $"key '{key}' must be an array");

    private static string RequiredString(TomlTable table, string key, string location) =>
        table.TryGetValue(key, out var value) && value is string text
            ? text
            : throw Invalid(location, $"key '{key}' must be a string");

    private static string[] RequiredStringArray(TomlTable table, string key, string location)
    {
        var values = RequiredArray(table, key, location);
        var result = new string[values.Count];
        for (var index = 0; index < values.Count; index++)
        {
            if (values[index] is not string text)
            {
                throw Invalid(location, $"key '{key}[{index}]' must be a string");
            }

            result[index] = text;
        }

        return result;
    }

    private static bool RequiredBoolean(TomlTable table, string key, string location) =>
        table.TryGetValue(key, out var value) && value is bool boolean
            ? boolean
            : throw Invalid(location, $"key '{key}' must be a boolean");

    private static int RequiredInt32(
        TomlTable table,
        string key,
        string location,
        int minimum)
    {
        if (!table.TryGetValue(key, out var value) || value is not long integer)
        {
            throw Invalid(location, $"key '{key}' must be an integer");
        }

        if (integer < minimum || integer > int.MaxValue)
        {
            throw Invalid(location, $"key '{key}' is outside [{minimum}, {int.MaxValue}]");
        }

        return checked((int)integer);
    }

    private static GoldenGenerality RequiredGenerality(
        TomlTable table,
        string key,
        string location)
    {
        var value = RequiredString(table, key, location);
        return Enum.TryParse<GoldenGenerality>(value, ignoreCase: false, out var parsed)
            && Enum.IsDefined(parsed)
            && string.Equals(parsed.ToString(), value, StringComparison.Ordinal)
                ? parsed
                : throw Invalid(location, $"key '{key}' has unknown generality '{value}'");
    }

    private static GoldenStratum RequiredStratum(TomlTable table, string key, string location)
    {
        var value = RequiredString(table, key, location);
        return Enum.TryParse<GoldenStratum>(value, ignoreCase: false, out var parsed)
            && Enum.IsDefined(parsed)
            && string.Equals(parsed.ToString(), value, StringComparison.Ordinal)
                ? parsed
                : throw Invalid(location, $"key '{key}' has unknown stratum '{value}'");
    }

    private static FormatException Invalid(string location, string message) =>
        new($"{location}: {message}");

    private static FormatException Invalid(string location, string message, Exception inner) =>
        new($"{location}: {message}", inner);
}
