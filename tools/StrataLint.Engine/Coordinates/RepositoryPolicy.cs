using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using Dunet;

namespace StrataLint.Engine;

public sealed record DomainSyntax(string Name, string Stratum, string Definition);

public sealed record ArtifactPolicy(
    ValidationProfile Profile,
    ImmutableHashSet<string> Selectors,
    ImmutableHashSet<string> PathSelectors);

public sealed class ValidatedPolicy
{
    private ValidatedPolicy(FileMapManifest manifest,
        ImmutableDictionary<DomainId, Stratum> domains,
        ImmutableArray<byte> canonicalDomainsBytes)
    {
        Manifest = manifest;
        Domains = domains;
        CanonicalFileMapBytes = FileMapCanonicalWriter.Write(manifest);
        CanonicalDomainsBytes = canonicalDomainsBytes;
        FileMapSha256 = Convert.ToHexStringLower(SHA256.HashData(CanonicalFileMapBytes.AsSpan()));
        DomainsSha256 = Convert.ToHexStringLower(SHA256.HashData(canonicalDomainsBytes.AsSpan()));
    }

    internal FileMapManifest Manifest { get; }
    public ImmutableDictionary<DomainId, Stratum> Domains { get; }
    public ImmutableDictionary<ArtifactKindId, ArtifactPolicy> ArtifactKinds => Manifest.ArtifactKinds;
    public ImmutableArray<byte> CanonicalFileMapBytes { get; }
    public ImmutableArray<byte> CanonicalDomainsBytes { get; }
    public string FileMapSha256 { get; }
    public string DomainsSha256 { get; }

    internal bool IsDigestionSource(RepoPath path) => Manifest.Match(path.Value) is [{ DigestionSource: true }];

    internal static ValidatedPolicy Create(FileMapManifest manifest, ImmutableArray<DomainSyntax> domains)
    {
        var domainBuilder = ImmutableDictionary.CreateBuilder<DomainId, Stratum>();
        var domainNames = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var domain in domains)
        {
            if (!DomainId.TryCreate(domain.Name, out var id)
                || !Enum.TryParse<Stratum>(domain.Stratum, ignoreCase: false, out var stratum)
                || !Enum.IsDefined(stratum) || domain.Stratum != stratum.ToString()
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

        return new ValidatedPolicy(manifest, domainBuilder.ToImmutable(), DomainsCanonicalWriter.Write(domains));
    }
}

[Union(EnableImplicitConversions = false)]
public partial record PolicyLoadOutcome
{
    public partial record Accepted
    {
        internal Accepted(ValidatedPolicy policy) => Policy = policy ?? throw new ArgumentNullException(nameof(policy));
        public ValidatedPolicy Policy { get; }
    }

    public partial record InfrastructureFailure(string Message);
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
