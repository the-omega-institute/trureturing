using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using Trureturing.Truth;

namespace StrataLint.Engine;

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
            return RegistryPolicyCompiler.Compile(syntax, domains);
        }
        catch (Exception exception) when (exception is DecoderFallbackException or FormatException)
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

    private static Dictionary<string, object?> ParseMappingDocument(ReadOnlySpan<byte> bytes, string label)
    {
        var text = new UTF8Encoding(false, true).GetString(bytes);
        YamlSubsetSyntaxGuard.RejectUnsupportedSyntax(text, "registry.yaml");
        return Mapping(YamlSubsetParser.Parse(text), label);
    }

    private static RegistrySyntax ProjectRegistrySyntax(IReadOnlyDictionary<string, object?> rootMap)
    {
        var unknown = rootMap.Keys.Where(key => !TopLevelKeys.Contains(key)).ToArray();
        var missing = TopLevelKeys.Where(key => !rootMap.ContainsKey(key)).ToArray();
        if (unknown.Length > 0 || missing.Length > 0)
        {
            throw new FormatException(
                $"Registry has unknown keys [{string.Join(", ", unknown)}] or missing keys [{string.Join(", ", missing)}].");
        }

        var schemaText = Scalar(rootMap["schema_version"], "schema_version");
        if (!int.TryParse(
                schemaText,
                NumberStyles.Integer,
                CultureInfo.InvariantCulture,
                out var schemaVersion))
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

    private static ImmutableArray<DomainSyntax> Domains(object? node)
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

    private static ImmutableArray<ArtifactKindSyntax> ArtifactKinds(object? node)
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

    private static Dictionary<string, object?> Mapping(object? node, string location)
    {
        if (node is not Dictionary<string, object?> mapping)
        {
            throw new FormatException($"{location} must be a mapping.");
        }

        return mapping;
    }

    private static ImmutableArray<string> ScalarSequence(object? node, string location)
    {
        if (node is not List<object?> sequence)
        {
            throw new FormatException($"{location} must be a sequence.");
        }

        return sequence.Select(child => Scalar(child, location)).ToImmutableArray();
    }

    private static string Scalar(object? node, string location) => node switch
    {
        string value => value,
        int value => value.ToString(CultureInfo.InvariantCulture),
        _ => throw new FormatException($"{location} must be a scalar."),
    };

    private static void RequireExact(
        IReadOnlyDictionary<string, object?> fields,
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
