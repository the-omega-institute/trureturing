using System.Buffers.Binary;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

namespace StrataLint.EngineeringScope.SelfLockProbe;

internal static class StrictArtifacts
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static T ReadJson<T>(string path)
    {
        EnsureRegularFile(path);
        var bytes = File.ReadAllBytes(path);
        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new InvalidDataException("artifact is not strict UTF-8", exception);
        }

        using var document = JsonDocument.Parse(text, new JsonDocumentOptions
        {
            AllowTrailingCommas = false,
            CommentHandling = JsonCommentHandling.Disallow,
            MaxDepth = 32,
        });
        RejectDuplicateMembers(document.RootElement);
        return JsonSerializer.Deserialize<T>(text, ContractJson.Options)
            ?? throw new InvalidDataException("artifact has a null top-level value");
    }

    internal static string DigestFile(string path)
    {
        EnsureRegularFile(path);
        return "sha256:" + Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path)))
            .ToLowerInvariant();
    }

    internal static string EvaluatorDigest(string controllerRoot)
    {
        var relativePaths = new[]
        {
            "Directory.Build.props",
            "Directory.Packages.props",
            "tools/scripts/workflow/pure-revert-detect.sh",
            "tools/scripts/workflow/self-lock-probe.sh",
            "tools/scripts/report/report-supervisor.sh",
            "tools/StrataLint.EngineeringScope/Program.cs",
            "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
            "tools/StrataLint.EngineeringScope/TestResultEvidence.cs",
            "tools/StrataLint.EngineeringScope/SelfLockProbe/EvidenceNormalizer.cs",
            "tools/StrataLint.EngineeringScope/SelfLockProbe/ProbeContracts.cs",
            "tools/StrataLint.EngineeringScope/SelfLockProbe/ProbeReducer.cs",
            "tools/StrataLint.EngineeringScope/SelfLockProbe/ProcessTools.cs",
            "tools/StrataLint.EngineeringScope/SelfLockProbe/Program.cs",
            "tools/StrataLint.EngineeringScope/SelfLockProbe/StrictArtifacts.cs",
        };
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        foreach (var relativePath in relativePaths.Order(StringComparer.Ordinal))
        {
            var path = Path.Combine(controllerRoot, relativePath);
            EnsureRegularFile(path);
            AppendLengthPrefixed(hash, StrictUtf8.GetBytes(relativePath));
            AppendLengthPrefixed(hash, File.ReadAllBytes(path));
        }
        return "sha256:" + Convert.ToHexString(hash.GetHashAndReset()).ToLowerInvariant();
    }

    internal static void EnsureSafeIdentity(string value, string field)
    {
        if (string.IsNullOrEmpty(value) || value.Length > 512)
        {
            throw new InvalidDataException($"{field} is empty or too long");
        }
        if (value.Any(static character => char.IsControl(character) || char.IsSurrogate(character)))
        {
            throw new InvalidDataException($"{field} contains a control or surrogate character");
        }
    }

    internal static void EnsureDigest(string value, string field)
    {
        if (value.Length != 71
            || !value.StartsWith("sha256:", StringComparison.Ordinal)
            || value[7..].Any(static character =>
                character is not (>= '0' and <= '9')
                and not (>= 'a' and <= 'f')))
        {
            throw new InvalidDataException($"{field} is not a canonical SHA-256 digest");
        }
    }

    internal static void EnsureObjectId(string value, string field)
    {
        if (value.Length is not (40 or 64)
            || value.Any(static character =>
                character is not (>= '0' and <= '9')
                and not (>= 'a' and <= 'f')))
        {
            throw new InvalidDataException($"{field} is not a canonical object id");
        }
    }

    internal static void EnsureRegularFile(string path)
    {
        if (!File.Exists(path))
        {
            throw new FileNotFoundException("required artifact is absent", path);
        }
        var attributes = File.GetAttributes(path);
        if ((attributes & (FileAttributes.Directory | FileAttributes.ReparsePoint)) != 0)
        {
            throw new InvalidDataException("artifact must be a regular non-link file");
        }
    }

    private static void RejectDuplicateMembers(JsonElement element)
    {
        if (element.ValueKind == JsonValueKind.Object)
        {
            var names = new HashSet<string>(StringComparer.Ordinal);
            foreach (var property in element.EnumerateObject())
            {
                if (!names.Add(property.Name))
                {
                    throw new InvalidDataException($"duplicate JSON member: {property.Name}");
                }
                RejectDuplicateMembers(property.Value);
            }
        }
        else if (element.ValueKind == JsonValueKind.Array)
        {
            foreach (var item in element.EnumerateArray())
            {
                RejectDuplicateMembers(item);
            }
        }
    }

    private static void AppendLengthPrefixed(IncrementalHash hash, byte[] bytes)
    {
        Span<byte> length = stackalloc byte[sizeof(long)];
        BinaryPrimitives.WriteInt64BigEndian(length, bytes.LongLength);
        hash.AppendData(length);
        hash.AppendData(bytes);
    }
}
