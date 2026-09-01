using System.Buffers.Binary;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

namespace StrataLint.EngineeringScope;

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
        var closure = ControllerClosure.Derive(controllerRoot);
        var files = ControllerClosure.ReadAtHead(controllerRoot, closure.EvaluatorPaths);
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        foreach (var relativePath in closure.EvaluatorPaths)
        {
            AppendLengthPrefixed(hash, StrictUtf8.GetBytes(relativePath));
            AppendLengthPrefixed(hash, files[relativePath]);
        }
        return "sha256:" + Convert.ToHexString(hash.GetHashAndReset()).ToLowerInvariant();
    }

    internal static string DigestBytes(byte[] bytes) =>
        "sha256:" + Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();

    internal static string ProducerDigest(string controllerRoot) =>
        DigestBytes(ControllerClosure.ReadAtHead(controllerRoot, ControllerClosure.ProducerPath));

    internal static string AuthorityReceiptPath(string controllerRoot, string bundleRoot)
    {
        var common = ProcessTools.GitText(controllerRoot, "rev-parse", "--git-common-dir");
        var commonPath = Path.GetFullPath(common, controllerRoot);
        if (!Directory.Exists(commonPath))
            throw new InvalidDataException("controller git common directory is absent");
        var authorityRoot = Path.Combine(commonPath, "self-lock-probe-authority");
        var bundleIdentity = SHA256.HashData(StrictUtf8.GetBytes(
            Path.TrimEndingDirectorySeparator(Path.GetFullPath(bundleRoot))));
        return Path.Combine(authorityRoot, Convert.ToHexString(bundleIdentity).ToLowerInvariant() + ".json");
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

internal static class EvidencePublisher
{
    internal static PublishedEvidenceContract Publish(
        string controllerRoot,
        string bundleRoot,
        string stagingBundle)
    {
        var controller = ProcessTools.RequireRepositoryRoot(controllerRoot);
        var bundle = Path.TrimEndingDirectorySeparator(Path.GetFullPath(bundleRoot));
        var staging = Path.TrimEndingDirectorySeparator(Path.GetFullPath(stagingBundle));
        if (Path.GetDirectoryName(staging) != bundle || Path.GetFileName(staging) != ".staging")
            throw new InvalidDataException("staging bundle must be the bundle-root .staging child");
        EnsureRegularDirectory(staging);
        Directory.CreateDirectory(bundle);

        var supervisorPath = Path.Combine(staging, "supervisor-result.json");
        StrictArtifacts.EnsureRegularFile(supervisorPath);
        var supervisorDigest = StrictArtifacts.DigestFile(supervisorPath);
        var artifacts = ReadTrxManifest(staging);
        var sentinel = new FinalizationSentinelContract(1, supervisorDigest, artifacts);
        var sentinelPath = Path.Combine(staging, "finalization.sentinel");
        WriteJson(sentinelPath, sentinel);
        var sentinelDigest = StrictArtifacts.DigestFile(sentinelPath);

        var closure = ControllerClosure.Derive(controller);
        var producerDigest = StrictArtifacts.ProducerDigest(controller);
        var publicationId = PublicationId(
            closure.Commit,
            producerDigest,
            bundle,
            supervisorDigest,
            sentinelDigest,
            artifacts);
        var payloadDirectory = "payloads/" + publicationId;
        var payloadRoot = Path.Combine(bundle, "payloads");
        var payload = Path.Combine(bundle, "payloads", publicationId);
        Directory.CreateDirectory(payloadRoot);
        if (Directory.Exists(payload))
        {
            ValidateExistingPayload(payload, supervisorDigest, sentinelDigest, artifacts);
            Directory.Delete(staging, recursive: true);
        }
        else
        {
            Directory.Move(staging, payload);
        }

        var receipt = new AuthorityReceiptContract(
            1,
            closure.Commit,
            ControllerClosure.ProducerPath,
            producerDigest,
            bundle,
            publicationId,
            payloadDirectory,
            sentinelDigest,
            supervisorDigest,
            artifacts);
        var receiptPath = StrictArtifacts.AuthorityReceiptPath(controller, bundle);
        var authorityRoot = Path.GetDirectoryName(receiptPath)!;
        Directory.CreateDirectory(authorityRoot);
        EnsureRegularDirectory(authorityRoot);
        WriteJsonAtomically(receiptPath, receipt);

        var pointer = new PublicationPointerContract(
            1,
            publicationId,
            payloadDirectory,
            sentinelDigest);
        WriteJsonAtomically(Path.Combine(bundle, "publication.json"), pointer);
        return new PublishedEvidenceContract(receiptPath, payload);
    }

    private static SentinelTrxContract[] ReadTrxManifest(string staging)
    {
        var trxRoot = Path.Combine(staging, "trx");
        EnsureRegularDirectory(trxRoot);
        return Directory.GetFiles(trxRoot, "*", SearchOption.TopDirectoryOnly)
            .Select(path =>
            {
                StrictArtifacts.EnsureRegularFile(path);
                var name = Path.GetFileName(path);
                if (name.Length == 0
                    || !name.EndsWith(".trx", StringComparison.Ordinal)
                    || name.Any(static character => char.IsControl(character)))
                {
                    throw new InvalidDataException("published TRX name is invalid");
                }
                return new SentinelTrxContract(name, StrictArtifacts.DigestFile(path));
            })
            .OrderBy(static artifact => artifact.FileName, StringComparer.Ordinal)
            .ToArray();
    }

    private static string PublicationId(
        string commit,
        string producerDigest,
        string bundle,
        string supervisorDigest,
        string sentinelDigest,
        IReadOnlyList<SentinelTrxContract> artifacts)
    {
        var preimage = JsonSerializer.SerializeToUtf8Bytes(new
        {
            commit,
            producer_digest = producerDigest,
            bundle,
            supervisor_digest = supervisorDigest,
            sentinel_digest = sentinelDigest,
            trx_artifacts = artifacts,
        }, ContractJson.Options);
        return Convert.ToHexString(SHA256.HashData(preimage)).ToLowerInvariant();
    }

    private static void ValidateExistingPayload(
        string payload,
        string supervisorDigest,
        string sentinelDigest,
        IReadOnlyList<SentinelTrxContract> artifacts)
    {
        EnsureRegularDirectory(payload);
        if (StrictArtifacts.DigestFile(Path.Combine(payload, "supervisor-result.json"))
                != supervisorDigest
            || StrictArtifacts.DigestFile(Path.Combine(payload, "finalization.sentinel"))
                != sentinelDigest)
        {
            throw new InvalidDataException("existing publication payload differs");
        }
        foreach (var artifact in artifacts)
        {
            if (StrictArtifacts.DigestFile(Path.Combine(payload, "trx", artifact.FileName))
                != artifact.Sha256)
            {
                throw new InvalidDataException("existing publication TRX differs");
            }
        }
    }

    private static void WriteJson<T>(string path, T value) =>
        File.WriteAllBytes(path, JsonSerializer.SerializeToUtf8Bytes(value, ContractJson.Options));

    private static void WriteJsonAtomically<T>(string path, T value)
    {
        var temporary = path + ".tmp-" + Environment.ProcessId;
        WriteJson(temporary, value);
        File.Move(temporary, path, overwrite: true);
    }

    private static void EnsureRegularDirectory(string path)
    {
        if (!Directory.Exists(path)
            || (File.GetAttributes(path) & FileAttributes.ReparsePoint) != 0)
        {
            throw new InvalidDataException("publication directory is absent or linked");
        }
    }
}
