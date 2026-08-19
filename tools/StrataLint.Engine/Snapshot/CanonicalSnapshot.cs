using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using Dunet;
using Trureturing.Truth;

namespace StrataLint.Engine;

public sealed class CanonicalFixedPoint
{
    private CanonicalFixedPoint(ImmutableArray<byte> bytes, string registrySha256)
    {
        Bytes = bytes;
        RegistrySha256 = registrySha256;
        Sha256 = Convert.ToHexStringLower(SHA256.HashData(bytes.AsSpan()));
    }

    public ImmutableArray<byte> Bytes { get; }

    public string Sha256 { get; }

    public string RegistrySha256 { get; }

    internal static CanonicalFixedPoint Create(ImmutableArray<byte> bytes, string registrySha256) =>
        new(bytes, registrySha256);
}

[Union(EnableImplicitConversions = false)]
public partial record CanonicalizationOutcome
{
    public partial record Accepted
    {
        internal Accepted(CanonicalFixedPoint capability) =>
            Capability = capability ?? throw new ArgumentNullException(nameof(capability));

        public CanonicalFixedPoint Capability { get; }
    }

    public partial record InfrastructureFailure(string Message);
}

public static class RepositoryCanonicalizer
{
    public static CanonicalizationOutcome Validate(RepositorySnapshot snapshot, ValidatedPolicy policy)
        => Validate(snapshot, policy, changes: null);

    public static CanonicalizationOutcome Validate(
        RepositorySnapshot snapshot,
        ValidatedPolicy policy,
        RawChangeSet? changes)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(policy);
        try
        {
            if (!snapshot.TryGetFile("Meta/registry.yaml", out var registry)
                || !registry.RawBytes.AsSpan().SequenceEqual(policy.CanonicalRegistryBytes.AsSpan()))
            {
                throw new FormatException("Repository registry bytes do not match the validated canonical policy.");
            }

            if (!snapshot.TryGetFile("Meta/domains.yaml", out var domains)
                || !domains.RawBytes.AsSpan().SequenceEqual(policy.CanonicalDomainsBytes.AsSpan()))
            {
                throw new FormatException("Repository domain bytes do not match the validated canonical policy.");
            }

            ValidateStructuredArtifacts(snapshot, policy, changes);

            var expectedEntries = snapshot.Files
                .OrderBy(static item => item.Key.Value, StringComparer.Ordinal)
                .Select(static item => SnapshotEntry.FromFile(item.Key, item.Value))
                .ToImmutableArray();
            var bytes = CanonicalSnapshotWriter.Write(policy.RegistrySha256, expectedEntries);
            return new CanonicalizationOutcome.Accepted(
                CanonicalFixedPoint.Create(bytes, policy.RegistrySha256));
        }
        catch (Exception exception) when (exception is FormatException or JsonException or DecoderFallbackException)
        {
            return new CanonicalizationOutcome.InfrastructureFailure(
                $"Repository canonicalization failed closed: {exception.Message}");
        }
    }

    private static void ValidateStructuredArtifacts(
        RepositorySnapshot snapshot,
        ValidatedPolicy policy,
        RawChangeSet? changes)
    {
        var paths = changes is null
            ? snapshot.Files.Keys.OrderBy(static path => path.Value, StringComparer.Ordinal)
            : changes.Paths.OrderBy(static path => path.Value, StringComparer.Ordinal);
        foreach (var path in paths)
        {
            if (!path.Value.StartsWith("Evidence/D5/", StringComparison.Ordinal))
            {
                continue;
            }

            if (!snapshot.Files.TryGetValue(path, out var file))
            {
                continue;
            }

            if (!RepositoryPathPolicy.TryResolve(path, policy, out var gid)
                || gid?.ToTarget() is not Target.Evidence evidence
                || !policy.ArtifactKinds.TryGetValue(evidence.ArtifactKind, out var artifact))
            {
                throw new FormatException(
                    $"Evidence artifact {path.Value} is outside the registry kind/selector whitelist.");
            }

            if (artifact.Profile is not (ValidationProfile.StructuredJson or ValidationProfile.StructuredYaml))
            {
                continue;
            }

            var canonical = artifact.Profile is ValidationProfile.StructuredJson
                ? StructuredCanonicalWriter.WriteJson(file.Text)
                : StructuredCanonicalWriter.WriteYaml(file.Text);
            if (!file.RawBytes.AsSpan().SequenceEqual(canonical.AsSpan()))
            {
                throw new FormatException($"Structured artifact {path.Value} bytes are not canonical.");
            }

            var canonicalText = Encoding.UTF8.GetString(canonical.AsSpan());
            var semanticIdentity = artifact.Profile is ValidationProfile.StructuredJson
                ? StructuredCanonicalWriter.JsonSemanticallyEqual(file.Text, canonicalText)
                : StructuredCanonicalWriter.YamlSemanticallyEqual(file.Text, canonicalText);
            var encodedAgain = artifact.Profile is ValidationProfile.StructuredJson
                ? StructuredCanonicalWriter.WriteJson(canonicalText)
                : StructuredCanonicalWriter.WriteYaml(canonicalText);
            if (!semanticIdentity || !canonical.AsSpan().SequenceEqual(encodedAgain.AsSpan()))
            {
                throw new FormatException(
                    $"Structured artifact {path.Value} canonical semantic/re-encode fixed point failed.");
            }
        }
    }
}

internal sealed record SnapshotEntry(RepoPath Path, int Length, string Sha256)
{
    internal static SnapshotEntry FromFile(RepoPath path, RepositoryFile file) => new(
        path,
        file.RawBytes.Length,
        Convert.ToHexStringLower(SHA256.HashData(file.RawBytes.AsSpan())));
}

internal static class CanonicalSnapshotWriter
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static readonly Regex HashPattern = new(
        "^[0-9a-f]{64}$",
        RegexOptions.CultureInvariant);

    internal static ImmutableArray<byte> Write(
        string registrySha256,
        ImmutableArray<SnapshotEntry> entries)
    {
        if (!HashPattern.IsMatch(registrySha256)
            || !entries.Select(static item => item.Path.Value)
                .SequenceEqual(entries.Select(static item => item.Path.Value).Order(StringComparer.Ordinal)))
        {
            throw new FormatException("Canonical snapshot writer received noncanonical input.");
        }

        var builder = new StringBuilder();
        builder.Append("schema_version: 1\n");
        builder.Append("registry_sha256: ").Append(registrySha256).Append('\n');
        builder.Append("files:\n");
        foreach (var entry in entries)
        {
            builder.Append("  - path_utf8_hex: ")
                .Append(Convert.ToHexStringLower(StrictUtf8.GetBytes(entry.Path.Value)))
                .Append('\n');
            builder.Append("    length: ").Append(entry.Length).Append('\n');
            builder.Append("    sha256: ").Append(entry.Sha256).Append('\n');
        }

        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }
}
