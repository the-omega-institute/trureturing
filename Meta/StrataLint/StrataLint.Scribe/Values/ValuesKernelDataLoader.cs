using System.Collections.Immutable;
using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Scribe;

internal static class ValuesKernelDataLoader
{
    internal const string RelativePath = "Golden/values-kernels.toml";
    internal const string LeanModulePath = "D5/S3/Constants/Values.lean";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly Regex Sha256Pattern = new(
        "^[0-9a-f]{64}$",
        RegexOptions.CultureInvariant);
    private static readonly string[] CommonKeys =
    [
        "computation", "definition", "error", "exact_value", "formula",
        "fractional_part_decimal_digits", "first_fibonacci_index", "id",
        "last_fibonacci_index", "lean_gid", "lean_statement_sha256", "method",
        "open_reason", "rational_denominator", "rational_numerator", "reference_error",
        "reference_value", "refs", "sqrt_five_denominator", "sqrt_five_numerator",
        "status", "term_count",
    ];

    internal static ImmutableArray<ValueDefinition> LoadRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        return LoadFile(Path.Combine(repositoryRoot, RelativePath));
    }

    internal static ImmutableArray<ValueDefinition> LoadFile(string path)
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

        RequireKeys(root, fullPath, "constants", "schema_version");
        if (RequiredLong(root, "schema_version", fullPath) != 1
            || root["constants"] is not TomlTableArray constants
            || constants.Count == 0)
        {
            throw Invalid(fullPath, "schema_version must be 1 and constants must contain at least one row");
        }

        var parsed = constants.Select((table, index) => Parse(table, $"{fullPath}:constants[{index}]")).ToArray();
        if (!parsed.Select(static item => item.Id)
                .SequenceEqual(parsed.Select(static item => item.Id).Order(StringComparer.Ordinal), StringComparer.Ordinal)
            || parsed.Select(static item => item.Id).Distinct(StringComparer.Ordinal).Count() != parsed.Length
            || parsed.Select(static item => item.LeanGid).Distinct(StringComparer.Ordinal).Count() != parsed.Length)
        {
            throw Invalid(fullPath, "constant ids and Lean GIDs must be unique and ids must be ordinally sorted");
        }

        var ids = parsed.Select(static item => item.Id).ToHashSet(StringComparer.Ordinal);
        foreach (var definition in parsed)
        {
            if (definition.References.Values.Any(reference => !ids.Contains(reference)))
            {
                throw Invalid(fullPath, $"constant {definition.Id} has a reference outside the catalog");
            }
        }

        return ImmutableArray.CreateRange(parsed);
    }

    private static ValueDefinition Parse(TomlTable table, string location)
    {
        RequireKeys(table, location, CommonKeys);
        var id = RequiredString(table, "id", location);
        var leanGid = RequiredString(table, "lean_gid", location);
        if (!Gid.TryParse(leanGid, out var parsedGid)
            || parsedGid.Path.Value != LeanModulePath
            || !leanGid.Contains('.', StringComparison.Ordinal)
            || leanGid.Contains("--", StringComparison.Ordinal))
        {
            throw Invalid(location, $"constant {id} has a noncanonical Lean declaration GID");
        }

        var statementSha = RequiredString(table, "lean_statement_sha256", location);
        if (!Sha256Pattern.IsMatch(statementSha))
        {
            throw Invalid(location, $"constant {id} has a malformed Lean statement SHA-256");
        }

        var status = RequiredString(table, "status", location) switch
        {
            "emitted" => ValueDefinitionStatus.Emitted,
            "registered-open" => ValueDefinitionStatus.RegisteredOpen,
            _ => throw Invalid(location, $"constant {id} has an unknown status"),
        };
        var computationKind = RequiredString(table, "computation", location);
        ValueComputation? computation = computationKind switch
        {
            "exact-quadratic" => ExactQuadratic(table, location),
            "cphi" => Cphi(table, location),
            "none" => null,
            _ => throw Invalid(location, $"constant {id} has an unknown computation kind"),
        };
        var error = OptionalString(table, "error", location);
        var exactValue = OptionalString(table, "exact_value", location);
        var openReason = OptionalString(table, "open_reason", location);
        if (status is ValueDefinitionStatus.Emitted
                && (computation is null || error is null || openReason is not null)
            || status is ValueDefinitionStatus.RegisteredOpen
                && (computation is not null || error is not null || exactValue is not null || openReason is null))
        {
            throw Invalid(location, $"constant {id} has fields inconsistent with status {status}");
        }

        return new ValueDefinition(
            id,
            leanGid,
            statementSha,
            status,
            RequiredString(table, "definition", location),
            OptionalString(table, "formula", location),
            References(table, location),
            exactValue,
            error,
            RequiredString(table, "method", location),
            RequiredString(table, "reference_value", location),
            RequiredString(table, "reference_error", location),
            computation,
            openReason);
    }

    private static ValueComputation.ExactQuadratic ExactQuadratic(
        TomlTable table,
        string location)
    {
        RejectKeys(table, location, CphiKeys());
        return new ValueComputation.ExactQuadratic(
            ExactRational.Create(
                RequiredLong(table, "rational_numerator", location),
                RequiredLong(table, "rational_denominator", location)),
            ExactRational.Create(
                RequiredLong(table, "sqrt_five_numerator", location),
                RequiredLong(table, "sqrt_five_denominator", location)));
    }

    private static ValueComputation.Cphi Cphi(TomlTable table, string location)
    {
        RejectKeys(table, location, ExactKeys());
        return new ValueComputation.Cphi(new CphiKernelSpec(
            RequiredInt(table, "term_count", location),
            RequiredInt(table, "fractional_part_decimal_digits", location),
            RequiredInt(table, "first_fibonacci_index", location),
            RequiredInt(table, "last_fibonacci_index", location)));
    }

    private static ImmutableDictionary<string, string> References(TomlTable table, string location)
    {
        if (!table.TryGetValue("refs", out var raw) || raw is not TomlTable refs)
        {
            throw Invalid(location, "refs must be an inline string table");
        }

        var builder = ImmutableDictionary.CreateBuilder<string, string>(StringComparer.Ordinal);
        foreach (var (key, value) in refs.OrderBy(static item => item.Key, StringComparer.Ordinal))
        {
            if (value is not string text || string.IsNullOrWhiteSpace(text) || !builder.TryAdd(key, text))
            {
                throw Invalid(location, "refs must contain unique non-empty string mappings");
            }
        }

        return builder.ToImmutable();
    }

    private static void RejectKeys(TomlTable table, string location, IEnumerable<string> keys)
    {
        var present = keys.Where(table.ContainsKey).ToArray();
        if (present.Length != 0)
        {
            throw Invalid(location, "unexpected computation fields: " + string.Join(", ", present));
        }
    }

    private static IEnumerable<string> ExactKeys() =>
        ["rational_denominator", "rational_numerator", "sqrt_five_denominator", "sqrt_five_numerator"];

    private static IEnumerable<string> CphiKeys() =>
        ["fractional_part_decimal_digits", "first_fibonacci_index", "last_fibonacci_index", "term_count"];

    private static int RequiredInt(TomlTable table, string key, string location)
    {
        var value = RequiredLong(table, key, location);
        if (value is < int.MinValue or > int.MaxValue)
        {
            throw Invalid(location, $"{key} is outside the Int32 range");
        }

        return (int)value;
    }

    private static long RequiredLong(TomlTable table, string key, string location) =>
        table.TryGetValue(key, out var raw) && raw is long value
            ? value
            : throw Invalid(location, $"{key} must be an integer");

    private static string RequiredString(TomlTable table, string key, string location) =>
        OptionalString(table, key, location)
        ?? throw Invalid(location, $"{key} must be a non-empty string");

    private static string? OptionalString(TomlTable table, string key, string location)
    {
        if (!table.TryGetValue(key, out var raw))
        {
            return null;
        }

        return raw is string value && !string.IsNullOrWhiteSpace(value)
            ? value
            : throw Invalid(location, $"{key} must be a non-empty string when present");
    }

    private static void RequireKeys(TomlTable table, string location, params string[] expected)
    {
        var allowed = expected.ToHashSet(StringComparer.Ordinal);
        var extras = table.Keys.Where(key => !allowed.Contains(key)).Order(StringComparer.Ordinal).ToArray();
        if (extras.Length != 0)
        {
            throw Invalid(location, "unknown keys: " + string.Join(", ", extras));
        }

        if (ReferenceEquals(expected, CommonKeys))
        {
            return;
        }

        var missing = expected.Where(key => !table.ContainsKey(key)).ToArray();
        if (missing.Length != 0)
        {
            throw Invalid(location, "missing keys: " + string.Join(", ", missing));
        }
    }

    private static FormatException Invalid(string location, string message, Exception? inner = null) =>
        new($"Invalid values kernel data at {location}: {message}.", inner);
}
