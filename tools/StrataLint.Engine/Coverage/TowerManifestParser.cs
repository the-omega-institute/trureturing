using System.Collections.Immutable;
using System.Text;
using Dunet;
using Trureturing.Truth;

namespace StrataLint.Engine;

[Union(EnableImplicitConversions = false)]
public partial record TowerManifestParseOutcome
{
    public partial record Loaded(TowerManifestSyntax Syntax);

    public partial record Invalid(string Message);
}

public static class TowerManifestParser
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static TowerManifestParseOutcome Parse(ReadOnlySpan<byte> bytes)
    {
        try
        {
            var root = Mapping(YamlSubsetParser.Parse(StrictUtf8.GetString(bytes)), "root");
            RequireKeys(root, "root", "schema_version", "components", "bootstrap");
            var schemaVersion = Integer(root, "schema_version", "root");
            var components = Sequence(root, "components", "root")
                .Select((item, index) => ParseComponent(item, index))
                .ToImmutableArray();
            var bootstrap = ParseBootstrap(Required(root, "bootstrap", "root"));
            return new TowerManifestParseOutcome.Loaded(
                new TowerManifestSyntax(schemaVersion, components, bootstrap));
        }
        catch (Exception exception) when (exception is FormatException or DecoderFallbackException)
        {
            return new TowerManifestParseOutcome.Invalid(exception.Message);
        }
    }

    private static TowerComponentSyntax ParseComponent(object? value, int index)
    {
        var label = $"components[{index}]";
        var mapping = Mapping(value, label);
        RequireKeys(mapping, label, "id", "kind", "members", "judged_by", "verification");
        return new TowerComponentSyntax(
            String(mapping, "id", label),
            String(mapping, "kind", label),
            Strings(mapping, "members", label),
            Strings(mapping, "judged_by", label),
            String(mapping, "verification", label));
    }

    private static TowerBootstrapSyntax ParseBootstrap(object? value)
    {
        const string label = "bootstrap";
        var mapping = Mapping(value, label);
        RequireKeys(
            mapping,
            label,
            "id",
            "judge",
            "reason",
            "genesis_event",
            "commit",
            "pull_request",
            "verification");
        return new TowerBootstrapSyntax(
            String(mapping, "id", label),
            String(mapping, "judge", label),
            String(mapping, "reason", label),
            String(mapping, "genesis_event", label),
            String(mapping, "commit", label),
            Integer(mapping, "pull_request", label),
            String(mapping, "verification", label));
    }

    private static Dictionary<string, object?> Mapping(object? value, string label) =>
        value as Dictionary<string, object?>
        ?? throw new FormatException($"tower {label} must be a mapping");

    private static List<object?> Sequence(
        IReadOnlyDictionary<string, object?> mapping,
        string key,
        string label) =>
        Required(mapping, key, label) as List<object?>
        ?? throw new FormatException($"tower {label}.{key} must be a sequence");

    private static ImmutableArray<string> Strings(
        IReadOnlyDictionary<string, object?> mapping,
        string key,
        string label) =>
        Sequence(mapping, key, label)
            .Select((item, index) => item as string
                ?? throw new FormatException($"tower {label}.{key}[{index}] must be a string"))
            .ToImmutableArray();

    private static string String(
        IReadOnlyDictionary<string, object?> mapping,
        string key,
        string label) =>
        Required(mapping, key, label) as string
        ?? throw new FormatException($"tower {label}.{key} must be a string");

    private static int Integer(
        IReadOnlyDictionary<string, object?> mapping,
        string key,
        string label) =>
        Required(mapping, key, label) is int value
            ? value
            : throw new FormatException($"tower {label}.{key} must be an integer");

    private static object? Required(
        IReadOnlyDictionary<string, object?> mapping,
        string key,
        string label) =>
        mapping.TryGetValue(key, out var value)
            ? value
            : throw new FormatException($"tower {label}.{key} is required");

    private static void RequireKeys(
        IReadOnlyDictionary<string, object?> mapping,
        string label,
        params string[] keys)
    {
        if (!mapping.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(keys))
        {
            throw new FormatException($"tower {label} keys are not canonical");
        }
    }
}
