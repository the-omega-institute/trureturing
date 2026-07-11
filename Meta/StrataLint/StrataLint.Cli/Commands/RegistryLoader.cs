using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using YamlDotNet.Core;
using YamlDotNet.Core.Events;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Cli;

public static class RegistryLoader
{
    private static readonly HashSet<string> TopLevelKeys = new(StringComparer.Ordinal)
    {
        "schema_version",
        "root_files",
        "governance_documents",
        "agent_files",
        "artifact_kinds",
    };

    public static RegistryLoadOutcome Load(
        ReadOnlySpan<byte> registryBytes,
        ReadOnlySpan<byte> domainsBytes)
    {
        try
        {
            var syntax = ParseRegistrySyntax(registryBytes);
            var domains = ParseDomainsSyntax(domainsBytes);
            var first = RegistryPolicyCompiler.Compile(syntax, domains, registryBytes, domainsBytes);
            if (first is RegistryLoadOutcome.InfrastructureFailure)
            {
                return first;
            }

            var accepted = (RegistryLoadOutcome.Accepted)first;
            var reparsed = ParseRegistrySyntax(accepted.Policy.CanonicalRegistryBytes.AsSpan());
            var reparsedDomains = ParseDomainsSyntax(accepted.Policy.CanonicalDomainsBytes.AsSpan());
            var second = RegistryPolicyCompiler.Compile(
                reparsed,
                reparsedDomains,
                accepted.Policy.CanonicalRegistryBytes.AsSpan(),
                accepted.Policy.CanonicalDomainsBytes.AsSpan());
            if (second is not RegistryLoadOutcome.Accepted secondAccepted
                || !SemanticallyEqual(syntax, reparsed)
                || !domains.SequenceEqual(reparsedDomains)
                || !accepted.Policy.CanonicalRegistryBytes.AsSpan()
                    .SequenceEqual(secondAccepted.Policy.CanonicalRegistryBytes.AsSpan())
                || !accepted.Policy.CanonicalDomainsBytes.AsSpan()
                    .SequenceEqual(secondAccepted.Policy.CanonicalDomainsBytes.AsSpan()))
            {
                throw new FormatException("Policy canonical parse/semantic/re-encode fixed point failed.");
            }

            return accepted;
        }
        catch (Exception exception) when (exception is DecoderFallbackException or YamlException or FormatException)
        {
            return new RegistryLoadOutcome.InfrastructureFailure(exception.Message);
        }
    }

    private static RegistrySyntax ParseRegistrySyntax(ReadOnlySpan<byte> bytes) =>
        ProjectRegistrySyntax(ParseMappingDocument(bytes, "registry"));

    private static ImmutableArray<DomainSyntax> ParseDomainsSyntax(ReadOnlySpan<byte> bytes)
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

    private static bool SemanticallyEqual(RegistrySyntax left, RegistrySyntax right) =>
        left.SchemaVersion == right.SchemaVersion
        && left.RootFiles.SequenceEqual(right.RootFiles, StringComparer.Ordinal)
        && left.GovernanceDocuments.SequenceEqual(right.GovernanceDocuments, StringComparer.Ordinal)
        && left.AgentFiles.SequenceEqual(right.AgentFiles, StringComparer.Ordinal)
        && left.ArtifactKinds.Length == right.ArtifactKinds.Length
        && left.ArtifactKinds.Zip(right.ArtifactKinds).All(static pair =>
            pair.First.Name == pair.Second.Name
            && pair.First.Profile == pair.Second.Profile
            && pair.First.Selectors.SequenceEqual(pair.Second.Selectors, StringComparer.Ordinal)
            && pair.First.PathSelectors.SequenceEqual(pair.Second.PathSelectors, StringComparer.Ordinal));

    private static void ScanEvents(string text)
    {
        var parser = new Parser(new StringReader(text));
        while (parser.MoveNext())
        {
            if (parser.Current is AnchorAlias)
            {
                throw new FormatException("YAML alias is forbidden in registry.yaml.");
            }

            if (parser.Current is not NodeEvent node)
            {
                continue;
            }

            if (!node.Anchor.IsEmpty)
            {
                throw new FormatException("YAML anchor is forbidden in registry.yaml.");
            }

            if (!node.Tag.IsEmpty && !node.Tag.IsNonSpecific)
            {
                throw new FormatException("YAML custom tag is forbidden in registry.yaml.");
            }
        }
    }

    private static RegistrySyntax ProjectRegistrySyntax(YamlMappingNode root)
    {
        var rootMap = Mapping(root, "registry root");
        var unknown = rootMap.Keys.Where(key => !TopLevelKeys.Contains(key)).ToArray();
        var missing = TopLevelKeys.Where(key => !rootMap.ContainsKey(key)).ToArray();
        if (unknown.Length > 0 || missing.Length > 0)
        {
            throw new FormatException(
                $"Registry has unknown keys [{string.Join(", ", unknown)}] or missing keys [{string.Join(", ", missing)}].");
        }

        var schemaText = Scalar(rootMap["schema_version"], "schema_version");
        if (!int.TryParse(schemaText, out var schemaVersion))
        {
            throw new FormatException("schema_version must be an integer.");
        }

        return new RegistrySyntax(
            schemaVersion,
            ScalarSequence(rootMap["root_files"], "root_files"),
            ScalarSequence(rootMap["governance_documents"], "governance_documents"),
            ScalarSequence(rootMap["agent_files"], "agent_files"),
            ArtifactKinds(rootMap["artifact_kinds"]));
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

    private static ImmutableArray<ArtifactKindSyntax> ArtifactKinds(YamlNode node)
    {
        var artifacts = Mapping(node, "artifact_kinds");
        var builder = ImmutableArray.CreateBuilder<ArtifactKindSyntax>();
        foreach (var (name, value) in artifacts)
        {
            var fields = Mapping(value, $"artifact kind {name}");
            RequireExact(fields, new[] { "profile", "selectors", "path_selectors" }, $"artifact kind {name}");
            builder.Add(new ArtifactKindSyntax(
                name,
                Scalar(fields["profile"], $"artifact kind {name} profile"),
                ScalarSequence(fields["selectors"], $"artifact kind {name} selectors"),
                ScalarSequence(fields["path_selectors"], $"artifact kind {name} path_selectors")));
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

    private static ImmutableArray<string> ScalarSequence(YamlNode node, string location)
    {
        if (node is not YamlSequenceNode sequence)
        {
            throw new FormatException($"{location} must be a sequence.");
        }

        return sequence.Children.Select(child => Scalar(child, location)).ToImmutableArray();
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
