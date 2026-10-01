using System.Collections.Immutable;
using System.Text;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Cli;

internal static class GateAuthorityRootCatalogLoader
{
    internal const string RelativePath = "Golden/gate-authority-roots.toml";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ImmutableArray<GateAuthorityRootDefinition> LoadRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        return Parse(File.ReadAllBytes(Path.Combine(repositoryRoot, RelativePath)));
    }

    internal static ImmutableArray<GateAuthorityRootDefinition> Parse(ReadOnlySpan<byte> bytes)
    {
        if (bytes.IsEmpty
            || bytes[^1] != (byte)'\n'
            || bytes.Contains((byte)'\r')
            || bytes.StartsWith(Encoding.UTF8.Preamble))
        {
            throw new FormatException("gate authority root catalog must be strict UTF-8 without BOM/CR and end in LF");
        }

        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("gate authority root catalog is not strict UTF-8", exception);
        }

        TomlTable table;
        try
        {
            table = TomlSerializer.Deserialize<TomlTable>(text)
                ?? throw new FormatException("gate authority root catalog is empty");
        }
        catch (Exception exception) when (exception is not FormatException)
        {
            throw new FormatException("gate authority root catalog is invalid TOML", exception);
        }

        RequireKeys(table, "catalog", "roots", "schema");
        if (table["schema"] is not string schema || schema != "gate-authority-roots-v1"
            || table["roots"] is not TomlTableArray rootTables || rootTables.Count == 0)
        {
            throw new FormatException("gate authority root catalog identity is invalid");
        }

        var roots = rootTables.Select((item, index) => ParseRoot(item, index)).ToImmutableArray();
        if (roots.Select(static root => root.RootId).Distinct(StringComparer.Ordinal).Count() != roots.Length
            || roots.Select(static root => root.RootId)
                .OrderBy(static value => Encoding.UTF8.GetBytes(value), ByteArrayComparer.Instance)
                .SequenceEqual(roots.Select(static root => root.RootId)) is false)
        {
            throw new FormatException("gate authority roots must have unique UTF-8-sorted root_id values");
        }

        return roots;
    }

    private static GateAuthorityRootDefinition ParseRoot(TomlTable table, int index)
    {
        RequireKeys(table, $"roots[{index}]", "entrypoint", "root_id");
        var rootId = RequiredString(table, "root_id", index);
        var entrypoint = RequiredString(table, "entrypoint", index);
        if (!IsSafeRelativePath(entrypoint))
        {
            throw new FormatException($"roots[{index}].entrypoint must be a normalized repository-relative path");
        }

        return new GateAuthorityRootDefinition(rootId, entrypoint);
    }

    private static string RequiredString(TomlTable table, string key, int index) =>
        table[key] is string { Length: > 0 } value && value == value.Trim()
            ? value
            : throw new FormatException($"roots[{index}].{key} is invalid");

    private static bool IsSafeRelativePath(string value) =>
        !value.StartsWith("/", StringComparison.Ordinal)
        && !value.Contains('\\')
        && value.Split('/').All(static segment => segment.Length > 0 && segment is not "." and not "..");

    private static void RequireKeys(TomlTable table, string location, params string[] keys)
    {
        if (!table.Keys.Order(StringComparer.Ordinal).SequenceEqual(keys.Order(StringComparer.Ordinal)))
        {
            throw new FormatException($"{location} fields are not closed");
        }
    }

    private sealed class ByteArrayComparer : IComparer<byte[]>
    {
        internal static readonly ByteArrayComparer Instance = new();

        public int Compare(byte[]? left, byte[]? right) =>
            (left, right) switch
            {
                (null, null) => 0,
                (null, _) => -1,
                (_, null) => 1,
                _ => left.AsSpan().SequenceCompareTo(right),
            };
    }
}
