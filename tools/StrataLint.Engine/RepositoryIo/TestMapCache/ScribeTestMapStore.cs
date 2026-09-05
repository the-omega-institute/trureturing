using System.Buffers.Binary;
using System.Collections.Concurrent;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Engine;

internal interface IScribeTestMapStorage
{
    bool TryRead(string name, out byte[] bytes);

    void Write(string name, byte[] bytes);
}

internal sealed class DirectoryScribeTestMapStorage(string root) : IScribeTestMapStorage
{
    private readonly string root = string.IsNullOrWhiteSpace(root)
        ? throw new ArgumentException("Test-map cache root must not be empty.", nameof(root))
        : Path.GetFullPath(root);

    public bool TryRead(string name, out byte[] bytes)
    {
        var path = Resolve(name);
        if (!File.Exists(path))
        {
            bytes = [];
            return false;
        }

        bytes = File.ReadAllBytes(path);
        return true;
    }

    public void Write(string name, byte[] bytes)
    {
        ArgumentNullException.ThrowIfNull(bytes);
        Directory.CreateDirectory(root);
        var destination = Resolve(name);
        var temporary = Path.Combine(root, $".{name}.{Path.GetRandomFileName()}.tmp");
        try
        {
            using (var stream = new FileStream(
                temporary,
                FileMode.CreateNew,
                FileAccess.Write,
                FileShare.None))
            {
                stream.Write(bytes);
                stream.Flush(flushToDisk: true);
            }

            File.Move(temporary, destination, overwrite: true);
        }
        finally
        {
            File.Delete(temporary);
        }
    }

    private string Resolve(string name)
    {
        if (string.IsNullOrEmpty(name)
            || !string.Equals(Path.GetFileName(name), name, StringComparison.Ordinal))
        {
            throw new ArgumentException("Test-map cache name must be a file name.", nameof(name));
        }

        return Path.Combine(root, name);
    }
}

internal sealed record ScribeTestMapCacheEvent(string InputDigest, string Outcome);

// C1 (1): Length-prefixed projection encoding binds tree-side input bytes: assuming no SHA-256
// collision, equal digests iff the projection bytes are equal.
//
// C1 (2): environment (rid/framework/dotnet_host/dotnet_sdk_version/evaluation_environment_digest)
// and metadata_digest bind the fixed MSBuild environment and Roslyn reference/nuspec contents.
// MSBuild can still read outside the projection in a full-tree checkout; that A-layer residual is unclosed.
//
// C1 (3): Cache provenance is the same as --judge-dll's judge-binaries cache: only dev push writes
// the base scope; PRs read it. Cache tampering has zero recorded incidents (CLAUDE.md 20''); no Engine MAC.
internal sealed class ScribeTestMapStore(
    IScribeTestMapStorage storage,
    ScribeTestMapEnvironment environment,
    Func<IEnumerable<ScribeCompilationProject>, IReadOnlyList<string>>? describeInputPaths = null)
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private readonly ConcurrentQueue<ScribeTestMapCacheEvent> events = new();

    // Events are observational; ordering between Current and ForkPoint is not a contract.
    internal IReadOnlyList<ScribeTestMapCacheEvent> Events => events.ToArray();

    internal ScribeTestMap GetOrDerive(
        RepositorySnapshot snapshot,
        Func<RepositorySnapshot, ScribeTestMap> derive)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(derive);
        var inputDigest = ComputeInputDigest(snapshot);
        string? metadataDigest = null;
        try
        {
            metadataDigest = ComputeMetadataDigest(snapshot, describeInputPaths);
        }
        catch (Exception exception)
        {
            Record(inputDigest, "invalid:metadata-read-failed-" + ExceptionReason(exception));
        }

        if (metadataDigest is not null && TryLoad(inputDigest, metadataDigest, out var cached))
        {
            Record(inputDigest, "hit");
            return cached;
        }

        var map = derive(snapshot);
        if (map.CompileQueryFindings.Count != 0)
        {
            Record(inputDigest, "store-skipped-compile-findings");
            return map;
        }

        try
        {
            if (metadataDigest is null) return map;
            if (!string.Equals(metadataDigest, ComputeMetadataDigest(snapshot, describeInputPaths), StringComparison.Ordinal))
            {
                Record(inputDigest, "store-skipped-metadata-changed");
                return map;
            }

            storage.Write(
                FileName(inputDigest),
                ScribeTestMapEnvelope.Create(
                    inputDigest,
                    metadataDigest,
                    environment,
                    map).Write());
            Record(inputDigest, "stored");
        }
        catch (Exception exception)
        {
            Record(inputDigest, "store-failed:" + ExceptionReason(exception));
        }

        return map;
    }

    internal static string ComputeInputDigest(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var inputs = snapshot.Files.Values
            .Where(static file => ScribeTestMapDeriver.IsDerivationInput(file.Path.Value))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToArray();
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        AppendHashString(hash, "test-map-input-v1");
        AppendHashInt32(hash, inputs.Length);
        foreach (var file in inputs)
        {
            AppendHashString(hash, file.Path.Value);
            AppendHashBytes(hash, file.RawBytes.AsSpan());
        }

        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    internal static string ComputeMetadataDigest(
        RepositorySnapshot snapshot,
        Func<IEnumerable<ScribeCompilationProject>, IReadOnlyList<string>>? describeInputPaths = null)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var projects = snapshot.Files.Values
            .Where(static file => file.Path.Value.EndsWith(".csproj", StringComparison.Ordinal))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .Select(file =>
            {
                var path = file.Path.Value;
                var lockPath = path[..(path.LastIndexOf('/') + 1)] + "packages.lock.json";
                return new ScribeCompilationProject(path, file.Text, "", [], [],
                    snapshot.Files.GetValueOrDefault(RepoPath.CreateKnown(lockPath))?.Text);
            });
        var paths = (describeInputPaths ?? ScribeMetadataReferenceResolver.DescribeInputPaths)(projects);
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        AppendHashString(hash, "test-map-metadata-v1");
        AppendHashInt32(hash, paths.Count);
        foreach (var path in paths)
        {
            AppendHashString(hash, path);
            var exists = File.Exists(path);
            AppendHashString(hash, exists ? "present" : "absent");
            if (exists)
            {
                AppendHashBytes(hash, SHA256.HashData(File.ReadAllBytes(path)));
            }
        }

        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    private bool TryLoad(string inputDigest, string metadataDigest, out ScribeTestMap map)
    {
        map = null!;
        byte[] bytes;
        try
        {
            if (!storage.TryRead(FileName(inputDigest), out bytes))
            {
                Record(inputDigest, "miss");
                return false;
            }
        }
        catch (Exception exception)
        {
            Record(inputDigest, "invalid:read-failed-" + ExceptionReason(exception));
            return false;
        }

        if (!ScribeTestMapEnvelope.TryRead(bytes, out var envelope, out var reason)
            || envelope is null)
        {
            Record(inputDigest, "invalid:" + reason);
            return false;
        }

        if (!string.Equals(envelope.InputDigest, inputDigest, StringComparison.Ordinal)
            || !string.Equals(FileName(envelope.InputDigest), FileName(inputDigest), StringComparison.Ordinal))
        {
            Record(inputDigest, "invalid:input-digest");
            return false;
        }

        if (!string.Equals(
                envelope.Producer.EngineMvid,
                ScribeTestMapProducer.Current.EngineMvid,
                StringComparison.Ordinal))
        {
            Record(inputDigest, "invalid:producer");
            return false;
        }

        if (!string.Equals(envelope.Environment.Rid, environment.Rid, StringComparison.Ordinal))
        {
            Record(inputDigest, "invalid:environment-rid");
            return false;
        }

        if (!string.Equals(envelope.Environment.Framework, environment.Framework, StringComparison.Ordinal))
        {
            Record(inputDigest, "invalid:environment-framework");
            return false;
        }

        if (!string.Equals(envelope.Environment.DotnetHost, environment.DotnetHost, StringComparison.Ordinal))
        {
            Record(inputDigest, "invalid:environment-dotnet-host");
            return false;
        }

        if (!string.Equals(
                envelope.Environment.DotnetSdkVersion,
                environment.DotnetSdkVersion,
                StringComparison.Ordinal))
        {
            Record(inputDigest, "invalid:environment-dotnet-sdk-version");
            return false;
        }

        if (!string.Equals(
                envelope.Environment.EvaluationEnvironmentDigest,
                environment.EvaluationEnvironmentDigest,
                StringComparison.Ordinal))
        {
            Record(inputDigest, "invalid:environment-evaluation-environment-digest");
            return false;
        }

        if (!string.Equals(envelope.MetadataDigest, metadataDigest, StringComparison.Ordinal))
        {
            Record(inputDigest, "invalid:metadata-digest");
            return false;
        }

        map = envelope.Map;
        return true;
    }

    private void Record(string inputDigest, string outcome) =>
        events.Enqueue(new ScribeTestMapCacheEvent(inputDigest, outcome));

    private static string FileName(string inputDigest) => inputDigest + ".json";

    private static string ExceptionReason(Exception exception) => exception.GetType().Name;

    private static void AppendHashString(IncrementalHash hash, string value) =>
        AppendHashBytes(hash, StrictUtf8.GetBytes(value));

    private static void AppendHashBytes(IncrementalHash hash, ReadOnlySpan<byte> value)
    {
        AppendHashInt32(hash, value.Length);
        hash.AppendData(value);
    }

    private static void AppendHashInt32(IncrementalHash hash, int value)
    {
        Span<byte> bytes = stackalloc byte[sizeof(int)];
        BinaryPrimitives.WriteInt32BigEndian(bytes, value);
        hash.AppendData(bytes);
    }
}
