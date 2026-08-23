using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Cli;

internal sealed record GateAuthorityRootDefinition(string RootId, string Entrypoint);

internal sealed record GateAuthorityRoot(
    string RootId,
    string Entrypoint,
    string EntrypointBlobSha256);

internal sealed record GateAuthority(
    string OldBuildSha256,
    ImmutableArray<GateAuthorityRoot> Roots);

internal static class GateAuthorityProducer
{
    internal static GateAuthority Create(string repositoryRoot, string oldBuildSha256)
    {
        if (!GateAuthorityReader.IsSha256(oldBuildSha256))
        {
            throw new FormatException("OLD_BUILD must be 64 lowercase hexadecimal characters.");
        }

        var definitions = GateAuthorityRootCatalogLoader.LoadRepository(repositoryRoot);
        var roots = definitions.Select(root =>
        {
            var path = Path.Combine(
                repositoryRoot,
                root.Entrypoint.Replace('/', Path.DirectorySeparatorChar));
            var bytes = File.ReadAllBytes(path);
            return new GateAuthorityRoot(
                root.RootId,
                root.Entrypoint,
                Convert.ToHexStringLower(SHA256.HashData(bytes)));
        }).ToImmutableArray();
        return new GateAuthority(oldBuildSha256, roots);
    }

    internal static byte[] Write(GateAuthority authority) =>
        StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
        {
            schema = "expected-gate-authority-v1",
            old_build_sha256 = authority.OldBuildSha256,
            roots = authority.Roots.Select(root => new
            {
                root_id = root.RootId,
                entrypoint = root.Entrypoint,
                entrypoint_blob_sha256 = root.EntrypointBlobSha256,
            }),
        })).ToArray();
}

internal static class GateAuthorityReader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static int Validate(
        ReadOnlySpan<byte> bytes,
        string? expectedAuthoritySha256,
        ImmutableArray<GateAuthorityRootDefinition> definitions)
    {
        try
        {
            ValidateCore(bytes, definitions);
            if (expectedAuthoritySha256 is not null
                && (!IsSha256(expectedAuthoritySha256)
                    || !string.Equals(
                        AuthoritySha256(bytes),
                        expectedAuthoritySha256,
                        StringComparison.Ordinal)))
            {
                return 2;
            }

            return 0;
        }
        catch (Exception exception) when (
            exception is JsonException or FormatException or DecoderFallbackException)
        {
            return 2;
        }
    }

    internal static string AuthoritySha256(ReadOnlySpan<byte> canonicalBytes)
    {
        var domain = Encoding.UTF8.GetBytes("expected-gate-authority-v1");
        var preimage = new byte[domain.Length + 1 + canonicalBytes.Length];
        domain.CopyTo(preimage, 0);
        canonicalBytes.CopyTo(preimage.AsSpan(domain.Length + 1));
        return Convert.ToHexStringLower(SHA256.HashData(preimage));
    }

    internal static bool IsSha256(string? value) =>
        value is { Length: 64 }
        && value.All(character => character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static void ValidateCore(
        ReadOnlySpan<byte> bytes,
        ImmutableArray<GateAuthorityRootDefinition> definitions)
    {
        _ = StrictUtf8.GetString(bytes);
        RejectDuplicateKeys(bytes);
        using var document = JsonDocument.Parse(bytes.ToArray());
        var canonical = StructuredCanonicalWriter.WriteJson(document.RootElement);
        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            throw new FormatException("authority is not RFC 8785 canonical JSON");
        }

        var root = document.RootElement;
        RequireObjectProperties(root, "old_build_sha256", "roots", "schema");
        if (root.GetProperty("schema").GetString() != "expected-gate-authority-v1"
            || !IsSha256(root.GetProperty("old_build_sha256").GetString()))
        {
            throw new FormatException("authority identity is invalid");
        }

        var roots = root.GetProperty("roots");
        if (roots.ValueKind != JsonValueKind.Array
            || roots.GetArrayLength() != definitions.Length)
        {
            throw new FormatException("authority root set is incomplete");
        }

        for (var index = 0; index < definitions.Length; index++)
        {
            var item = roots[index];
            RequireObjectProperties(item, "entrypoint", "entrypoint_blob_sha256", "root_id");
            var expected = definitions[index];
            if (item.GetProperty("root_id").GetString() != expected.RootId
                || item.GetProperty("entrypoint").GetString() != expected.Entrypoint
                || !IsSha256(item.GetProperty("entrypoint_blob_sha256").GetString()))
            {
                throw new FormatException("authority root is invalid");
            }
        }
    }

    private static void RequireObjectProperties(JsonElement element, params string[] expected)
    {
        if (element.ValueKind != JsonValueKind.Object
            || !element.EnumerateObject().Select(property => property.Name).SequenceEqual(expected))
        {
            throw new FormatException("authority object fields are not closed and canonical");
        }
    }

    private static void RejectDuplicateKeys(ReadOnlySpan<byte> bytes)
    {
        var reader = new Utf8JsonReader(bytes, true, default);
        var objectKeys = new Stack<HashSet<string>>();
        while (reader.Read())
        {
            if (reader.TokenType == JsonTokenType.StartObject)
            {
                objectKeys.Push(new HashSet<string>(StringComparer.Ordinal));
            }
            else if (reader.TokenType == JsonTokenType.EndObject)
            {
                objectKeys.Pop();
            }
            else if (reader.TokenType == JsonTokenType.PropertyName
                && !objectKeys.Peek().Add(reader.GetString()!))
            {
                throw new FormatException("duplicate JSON property");
            }
        }
    }
}

internal static class GateAuthorityCommand
{
    internal static ExplicitCommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 1 && arguments[0] == "--check")
        {
            return Check(repositoryRoot);
        }

        return Usage();
    }

    private static ExplicitCommandResult Check(string repositoryRoot)
    {
        try
        {
            var definitions = GateAuthorityRootCatalogLoader.LoadRepository(repositoryRoot);
            var initialFindings = definitions
                .SelectMany(definition => CheckRoot(repositoryRoot, definition, null))
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (initialFindings.Length != 0)
            {
                return InvalidContent(initialFindings);
            }

            var authority = GateAuthorityProducer.Create(repositoryRoot, new string('0', 64));
            var bytes = GateAuthorityProducer.Write(authority);
            if (GateAuthorityReader.Validate(bytes, null, definitions) != 0)
            {
                throw new FormatException("generated authority failed strict validation");
            }

            var findings = definitions.Zip(authority.Roots)
                .SelectMany(pair => CheckRoot(
                    repositoryRoot,
                    pair.First,
                    pair.Second.EntrypointBlobSha256))
                .Order(StringComparer.Ordinal)
                .ToArray();
            return findings.Length == 0
                ? new ExplicitCommandResult(
                    0,
                    $"GATE_AUTHORITY_CHECK roots={definitions.Length} "
                        + $"authority_sha256={GateAuthorityReader.AuthoritySha256(bytes)}\n",
                    string.Empty)
                : InvalidContent(findings);
        }
        catch (Exception exception) when (
            exception is IOException
                or UnauthorizedAccessException
                or FormatException
                or DecoderFallbackException)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"GATE_AUTHORITY_INVALID {exception.Message}\n");
        }
    }

    private static IEnumerable<string> CheckRoot(
        string repositoryRoot,
        GateAuthorityRootDefinition definition,
        string? expectedBlobSha256)
    {
        var path = Path.Combine(
            repositoryRoot,
            definition.Entrypoint.Replace('/', Path.DirectorySeparatorChar));
        if (!File.Exists(path))
        {
            return [$"root={definition.RootId} entrypoint={definition.Entrypoint} is missing"];
        }

        var bytes = File.ReadAllBytes(path);
        var blobSha256 = Convert.ToHexStringLower(SHA256.HashData(bytes));
        if (expectedBlobSha256 is not null
            && !string.Equals(blobSha256, expectedBlobSha256, StringComparison.Ordinal))
        {
            return [$"root={definition.RootId} entrypoint={definition.Entrypoint} blob sha changed during check"];
        }

        var separator = definition.RootId.IndexOf('/', StringComparison.Ordinal);
        if (separator <= 0 || separator == definition.RootId.Length - 1)
        {
            return [$"root={definition.RootId} has no target segment"];
        }

        var target = definition.RootId[(separator + 1)..];
        var body = new UTF8Encoding(false, true).GetString(bytes);
        return body.Contains(target, StringComparison.Ordinal)
            ? []
            : [$"root={definition.RootId} entrypoint={definition.Entrypoint} no longer mentions target={target}"];
    }

    private static ExplicitCommandResult InvalidContent(IEnumerable<string> findings) => new(
        1,
        string.Empty,
        string.Concat(findings.Select(static finding =>
            $"GATE_AUTHORITY_STALE {finding}\n")));

    private static ExplicitCommandResult Usage() => new(
        2,
        string.Empty,
        "USAGE: StrataLint gate-authority --check\n");
}
