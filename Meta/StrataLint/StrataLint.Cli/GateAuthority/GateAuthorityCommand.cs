using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record GateAuthorityRootDefinition(string RootId, string Entrypoint);

internal static class GateAuthorityRootCatalog
{
    internal static readonly ImmutableArray<GateAuthorityRootDefinition> All =
    [
        new("Makefile/echo-verify", "Makefile"),
        new("Makefile/emit-check", "Makefile"),
        new("Makefile/gate", "Makefile"),
        new("Makefile/preflight", "Makefile"),
        new("ci.yml/baseline-admission", ".github/workflows/ci.yml"),
        new("ci.yml/candidate-engineering", ".github/workflows/ci.yml"),
        new("ci.yml/lean-inspect", ".github/workflows/ci.yml"),
        new("harness-gate.sh/admission", ".github/scripts/harness-gate.sh"),
        new("harness-gate.sh/build-candidate", ".github/scripts/harness-gate.sh"),
        new("harness-gate.sh/build-judge", ".github/scripts/harness-gate.sh"),
        new("harness-gate.sh/conservative", ".github/scripts/harness-gate.sh"),
        new("harness-gate.sh/echo-verify", ".github/scripts/harness-gate.sh"),
        new("harness-gate.sh/selftest", ".github/scripts/harness-gate.sh"),
        new("local-harness-gate.sh/admission", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        new("local-harness-gate.sh/echo-verify-bootstrap", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        new("local-harness-gate.sh/emit-check", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        new("local-harness-gate.sh/engineering-dotnet", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        new("local-harness-gate.sh/engineering-selftest", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        new("local-harness-gate.sh/engineering-test", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        new("local-harness-gate.sh/lean-reports", "Meta/StrataLint/scripts/local-harness-gate.sh"),
        new("local-harness-gate.sh/setup", "Meta/StrataLint/scripts/local-harness-gate.sh"),
    ];
}

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

        var roots = GateAuthorityRootCatalog.All.Select(root =>
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

    internal static int Validate(ReadOnlySpan<byte> bytes, string? expectedAuthoritySha256)
    {
        try
        {
            ValidateCore(bytes);
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

    private static void ValidateCore(ReadOnlySpan<byte> bytes)
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
            || roots.GetArrayLength() != GateAuthorityRootCatalog.All.Length)
        {
            throw new FormatException("authority root set is incomplete");
        }

        for (var index = 0; index < GateAuthorityRootCatalog.All.Length; index++)
        {
            var item = roots[index];
            RequireObjectProperties(item, "entrypoint", "entrypoint_blob_sha256", "root_id");
            var expected = GateAuthorityRootCatalog.All[index];
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
    internal static ExplicitCommandResult Run(
        string repositoryRoot,
        string? oldBuildSha256,
        string? outputPath)
    {
        if (!GateAuthorityReader.IsSha256(oldBuildSha256) || string.IsNullOrEmpty(outputPath))
        {
            return Usage();
        }

        try
        {
            var bytes = GateAuthorityProducer.Write(
                GateAuthorityProducer.Create(repositoryRoot, oldBuildSha256!));
            if (GateAuthorityReader.Validate(bytes, null) != 0)
            {
                return Usage();
            }

            using var stream = new FileStream(
                outputPath,
                FileMode.Create,
                FileAccess.Write,
                FileShare.None);
            stream.Write(bytes);
            return new ExplicitCommandResult(0, string.Empty, string.Empty);
        }
        catch (Exception exception) when (
            exception is IOException or UnauthorizedAccessException or FormatException)
        {
            return new ExplicitCommandResult(2, string.Empty, $"GATE_AUTHORITY_INVALID {exception.Message}\n");
        }
    }

    internal static ExplicitCommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 4
            || arguments[0] != "--old-build"
            || arguments[2] != "--out")
        {
            return Usage();
        }

        return Run(repositoryRoot, arguments[1], arguments[3]);
    }

    private static ExplicitCommandResult Usage() => new(
        2,
        string.Empty,
        "USAGE: StrataLint gate-authority --old-build SHA256 --out FILE\n");
}
