using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using YamlDotNet.Core;
using YamlDotNet.Core.Events;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Cli;

internal static class DomainsLoader
{
    internal static ImmutableArray<DomainSyntax> Parse(ReadOnlySpan<byte> bytes)
    {
        var root = Mapping(ParseMappingDocument(bytes, "domain vocabulary"), "domain vocabulary root");
        RequireExact(root, new[] { "domains" }, "domain vocabulary root");
        return Domains(root["domains"]);
    }

    private static YamlMappingNode ParseMappingDocument(ReadOnlySpan<byte> bytes, string label)
    {
        var text = new UTF8Encoding(false, true).GetString(bytes);
        ScanEvents(text);
        var stream = new YamlStream();
        stream.Load(new StringReader(text));
        if (stream.Documents.Count != 1 || stream.Documents[0].RootNode is not YamlMappingNode root)
        {
            throw new FormatException($"{label} must contain exactly one mapping document.");
        }

        return root;
    }

    private static void ScanEvents(string text)
    {
        var parser = new Parser(new StringReader(text));
        while (parser.MoveNext())
        {
            if (parser.Current is AnchorAlias)
            {
                throw new FormatException("YAML alias is forbidden in domains.yaml.");
            }

            if (parser.Current is not NodeEvent node)
            {
                continue;
            }

            if (!node.Anchor.IsEmpty)
            {
                throw new FormatException("YAML anchor is forbidden in domains.yaml.");
            }

            if (!node.Tag.IsEmpty && !node.Tag.IsNonSpecific)
            {
                throw new FormatException("YAML custom tag is forbidden in domains.yaml.");
            }
        }
    }

    private static ImmutableArray<DomainSyntax> Domains(YamlNode node)
    {
        var domains = Mapping(node, "domains");
        var builder = ImmutableArray.CreateBuilder<DomainSyntax>();
        foreach (var (name, value) in domains)
        {
            var fields = Mapping(value, $"domain {name}");
            RequireExact(fields, new[] { "stratum", "definition" }, $"domain {name}");
            builder.Add(new DomainSyntax(
                name,
                Scalar(fields["stratum"], $"domain {name} stratum"),
                Scalar(fields["definition"], $"domain {name} definition")));
        }

        return builder.ToImmutable();
    }

    private static Dictionary<string, YamlNode> Mapping(YamlNode node, string location)
    {
        if (node is not YamlMappingNode mapping)
        {
            throw new FormatException($"{location} must be a mapping.");
        }

        var result = new Dictionary<string, YamlNode>(StringComparer.Ordinal);
        foreach (var pair in mapping.Children)
        {
            var key = Scalar(pair.Key, $"{location} key");
            if (key == "<<")
            {
                throw new FormatException($"YAML merge key is forbidden at {location}.");
            }

            if (!result.TryAdd(key, pair.Value))
            {
                throw new FormatException($"Duplicate key {key} at {location}.");
            }
        }

        return result;
    }

    private static string Scalar(YamlNode node, string location) =>
        node is YamlScalarNode { Value: not null } scalar
            ? scalar.Value
            : throw new FormatException($"{location} must be a scalar.");

    private static void RequireExact(
        IReadOnlyDictionary<string, YamlNode> fields,
        IEnumerable<string> expected,
        string location)
    {
        var expectedSet = expected.ToHashSet(StringComparer.Ordinal);
        var unknown = fields.Keys.Where(key => !expectedSet.Contains(key)).ToArray();
        var missing = expectedSet.Where(key => !fields.ContainsKey(key)).ToArray();
        if (unknown.Length > 0 || missing.Length > 0)
        {
            throw new FormatException(
                $"{location} has unknown keys [{string.Join(", ", unknown)}] or missing keys [{string.Join(", ", missing)}].");
        }
    }
}
