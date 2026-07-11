using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.RegularExpressions;
using Dunet;

namespace StrataLint.Engine;

public sealed record DomainSyntax(string Name, string Stratum, string Definition);

public sealed record ArtifactKindSyntax(
    string Name,
    string Profile,
    ImmutableArray<string> Selectors,
    ImmutableArray<string> PathSelectors);

public sealed record RegistrySyntax(
    int SchemaVersion,
    ImmutableArray<string> RootFiles,
    ImmutableArray<string> GovernanceDocuments,
    ImmutableArray<string> AgentFiles,
    ImmutableArray<ArtifactKindSyntax> ArtifactKinds);

public sealed record ArtifactPolicy(
    ValidationProfile Profile,
    ImmutableHashSet<string> Selectors,
    ImmutableHashSet<string> PathSelectors);

public sealed class ValidatedPolicy
{
    private ValidatedPolicy(
        ImmutableHashSet<RepoPath> rootFiles,
        ImmutableHashSet<RepoPath> governanceDocuments,
        ImmutableHashSet<string> agentFiles,
        ImmutableDictionary<DomainId, Stratum> domains,
        ImmutableDictionary<ArtifactKindId, ArtifactPolicy> artifactKinds,
        ImmutableArray<byte> canonicalRegistryBytes,
        ImmutableArray<byte> canonicalDomainsBytes)
    {
        RootFiles = rootFiles;
        GovernanceDocuments = governanceDocuments;
        AgentFiles = agentFiles;
        Domains = domains;
        ArtifactKinds = artifactKinds;
        CanonicalRegistryBytes = canonicalRegistryBytes;
        CanonicalDomainsBytes = canonicalDomainsBytes;
        RegistrySha256 = Convert.ToHexStringLower(SHA256.HashData(canonicalRegistryBytes.AsSpan()));
        DomainsSha256 = Convert.ToHexStringLower(SHA256.HashData(canonicalDomainsBytes.AsSpan()));
    }

    public ImmutableHashSet<RepoPath> RootFiles { get; }

    public ImmutableHashSet<RepoPath> GovernanceDocuments { get; }

    public ImmutableHashSet<string> AgentFiles { get; }

    public ImmutableDictionary<DomainId, Stratum> Domains { get; }

    public ImmutableDictionary<ArtifactKindId, ArtifactPolicy> ArtifactKinds { get; }

    public ImmutableArray<byte> CanonicalRegistryBytes { get; }

    public ImmutableArray<byte> CanonicalDomainsBytes { get; }

    public string RegistrySha256 { get; }

    public string DomainsSha256 { get; }

    internal static ValidatedPolicy Create(
        ImmutableHashSet<RepoPath> rootFiles,
        ImmutableHashSet<RepoPath> governanceDocuments,
        ImmutableHashSet<string> agentFiles,
        ImmutableDictionary<DomainId, Stratum> domains,
        ImmutableDictionary<ArtifactKindId, ArtifactPolicy> artifactKinds,
        ImmutableArray<byte> canonicalRegistryBytes,
        ImmutableArray<byte> canonicalDomainsBytes) =>
        new(
            rootFiles,
            governanceDocuments,
            agentFiles,
            domains,
            artifactKinds,
            canonicalRegistryBytes,
            canonicalDomainsBytes);
}

[Union(EnableImplicitConversions = false)]
public partial record RegistryLoadOutcome
{
    public partial record Accepted(ValidatedPolicy Policy);

    public partial record InfrastructureFailure(string Message);
}

public static class RegistryPolicyCompiler
{
    private static readonly Regex SafeSelectorPattern = new(
        "^[A-Za-z0-9_.-]+$",
        RegexOptions.CultureInvariant);

    private static readonly ImmutableHashSet<string> KnownPathSelectors =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "experiments",
            "formal",
            "kernels",
            "special",
            "values");

    public static RegistryLoadOutcome Compile(
        RegistrySyntax syntax,
        ImmutableArray<DomainSyntax> domains,
        ReadOnlySpan<byte> rawRegistryBytes,
        ReadOnlySpan<byte> rawDomainsBytes)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        try
        {
            if (syntax.SchemaVersion != 1)
            {
                throw new FormatException("Unknown registry schema_version; expected 1.");
            }

            var rootFiles = ValidatePaths(syntax.RootFiles, "root_files");
            var governance = ValidatePaths(syntax.GovernanceDocuments, "governance_documents");
            var agentFiles = ValidateStrings(syntax.AgentFiles, "agent_files", static value =>
                RepoPath.TryCreate(value, out _) && !value.Contains('/', StringComparison.Ordinal));

            var domainBuilder = ImmutableDictionary.CreateBuilder<DomainId, Stratum>();
            var domainNames = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
            foreach (var domain in domains)
            {
                if (!DomainId.TryCreate(domain.Name, out var id)
                    || !Enum.TryParse<Stratum>(domain.Stratum, ignoreCase: false, out var stratum)
                    || string.IsNullOrWhiteSpace(domain.Definition))
                {
                    throw new FormatException($"Invalid domain entry: {domain.Name}.");
                }

                if (!domainNames.Add(id.Value) || !domainBuilder.TryAdd(id, stratum))
                {
                    throw new FormatException($"Duplicate or case-colliding domain: {id.Value}.");
                }
            }

            if (domainBuilder.Count == 0)
            {
                throw new FormatException("Domain vocabulary must not be empty.");
            }

            var artifactBuilder = ImmutableDictionary.CreateBuilder<ArtifactKindId, ArtifactPolicy>();
            var artifactNames = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
            foreach (var artifact in syntax.ArtifactKinds)
            {
                if (!ArtifactKindId.TryCreate(artifact.Name, out var id))
                {
                    throw new FormatException($"Invalid artifact kind: {artifact.Name}.");
                }

                var profile = ParseProfile(artifact.Profile);
                var selectors = ValidateStrings(
                    artifact.Selectors,
                    $"artifact kind {id.Value} selectors",
                    static value => value is not "." and not ".." && SafeSelectorPattern.IsMatch(value));
                var pathSelectors = ValidateStrings(
                    artifact.PathSelectors,
                    $"artifact kind {id.Value} path_selectors",
                    KnownPathSelectors.Contains);
                if (selectors.Count == 0 || pathSelectors.Count == 0)
                {
                    throw new FormatException($"Artifact kind {id.Value} has an empty selector set.");
                }

                if (!artifactNames.Add(id.Value)
                    || !artifactBuilder.TryAdd(id, new ArtifactPolicy(profile, selectors, pathSelectors)))
                {
                    throw new FormatException($"Duplicate or case-colliding artifact kind: {id.Value}.");
                }
            }

            if (artifactBuilder.Count == 0)
            {
                throw new FormatException("Registry artifact_kinds must not be empty.");
            }

            var canonicalRegistryBytes = RegistryCanonicalWriter.Write(syntax);
            if (!rawRegistryBytes.SequenceEqual(canonicalRegistryBytes.AsSpan()))
            {
                throw new FormatException("Registry bytes are not canonical.");
            }

            var canonicalDomainsBytes = DomainsCanonicalWriter.Write(domains);
            if (!rawDomainsBytes.SequenceEqual(canonicalDomainsBytes.AsSpan()))
            {
                throw new FormatException("Domain vocabulary bytes are not canonical.");
            }

            var policy = ValidatedPolicy.Create(
                rootFiles,
                governance,
                agentFiles,
                domainBuilder.ToImmutable(),
                artifactBuilder.ToImmutable(),
                canonicalRegistryBytes,
                canonicalDomainsBytes);
            return new RegistryLoadOutcome.Accepted(policy);
        }
        catch (FormatException exception)
        {
            return new RegistryLoadOutcome.InfrastructureFailure(exception.Message);
        }
    }

    private static ImmutableHashSet<RepoPath> ValidatePaths(
        ImmutableArray<string> values,
        string label)
    {
        var builder = ImmutableHashSet.CreateBuilder<RepoPath>();
        var folded = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var value in values)
        {
            if (!RepoPath.TryCreate(value, out var path) || !folded.Add(path.Value) || !builder.Add(path))
            {
                throw new FormatException($"Invalid, duplicate, or case-colliding {label} path: {value}.");
            }
        }

        return builder.ToImmutable();
    }

    private static ImmutableHashSet<string> ValidateStrings(
        ImmutableArray<string> values,
        string label,
        Func<string, bool> predicate)
    {
        var builder = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var folded = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var value in values)
        {
            if (!predicate(value) || !folded.Add(value) || !builder.Add(value))
            {
                throw new FormatException($"Invalid, duplicate, or case-colliding {label} value: {value}.");
            }
        }

        return builder.ToImmutable();
    }

    private static ValidationProfile ParseProfile(string profile) => profile switch
    {
        "structured-json" => new ValidationProfile.StructuredJson(),
        "structured-yaml" => new ValidationProfile.StructuredYaml(),
        "lean-module" => new ValidationProfile.LeanModule(),
        "opaque-text" => new ValidationProfile.OpaqueText(),
        _ => throw new FormatException($"Unknown or dangling ValidationProfile reference: {profile}."),
    };
}

internal static class RegistryCanonicalWriter
{
    private static readonly JsonSerializerOptions StringOptions = new()
    {
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    internal static ImmutableArray<byte> Write(RegistrySyntax syntax)
    {
        var builder = new StringBuilder();
        builder.Append("schema_version: 1\n");
        AppendList(builder, "root_files", syntax.RootFiles);
        AppendList(builder, "governance_documents", syntax.GovernanceDocuments);
        AppendList(builder, "agent_files", syntax.AgentFiles);
        builder.Append("artifact_kinds:\n");
        foreach (var artifact in syntax.ArtifactKinds.OrderBy(static item => item.Name, StringComparer.Ordinal))
        {
            builder.Append("  ").Append(artifact.Name).Append(":\n");
            builder.Append("    profile: ").Append(artifact.Profile).Append('\n');
            AppendNestedList(builder, "selectors", artifact.Selectors);
            AppendNestedList(builder, "path_selectors", artifact.PathSelectors);
        }

        return ImmutableArray.CreateRange(new UTF8Encoding(false, true).GetBytes(builder.ToString()));
    }

    private static void AppendList(StringBuilder builder, string key, IEnumerable<string> values)
    {
        builder.Append(key).Append(":\n");
        foreach (var value in values.Order(StringComparer.Ordinal))
        {
            builder.Append("  - ").Append(Quote(value)).Append('\n');
        }
    }

    private static void AppendNestedList(StringBuilder builder, string key, IEnumerable<string> values)
    {
        builder.Append("    ").Append(key).Append(":\n");
        foreach (var value in values.Order(StringComparer.Ordinal))
        {
            builder.Append("      - ").Append(Quote(value)).Append('\n');
        }
    }

    private static string Quote(string value) => JsonSerializer.Serialize(value, StringOptions);
}

internal static class DomainsCanonicalWriter
{
    internal static ImmutableArray<byte> Write(ImmutableArray<DomainSyntax> domains)
    {
        var builder = new StringBuilder("domains:\n");
        foreach (var domain in domains.OrderBy(static item => item.Name, StringComparer.Ordinal))
        {
            if (domain.Definition.Trim() != domain.Definition
                || domain.Definition.IndexOfAny(['\r', '\n', ':', '#']) >= 0
                || domain.Definition is "null" or "~" or "[]")
            {
                throw new FormatException($"Domain {domain.Name} definition is not a canonical plain scalar.");
            }

            builder.Append("  ").Append(domain.Name).Append(":\n");
            builder.Append("    stratum: ").Append(domain.Stratum).Append('\n');
            builder.Append("    definition: ").Append(domain.Definition).Append('\n');
        }

        return ImmutableArray.CreateRange(new UTF8Encoding(false, true).GetBytes(builder.ToString()));
    }
}
