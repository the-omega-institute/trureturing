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

internal sealed class ScribeTestMapStore(
    IScribeTestMapStorage storage,
    ScribeTestMapEnvironment environment)
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private readonly ConcurrentQueue<ScribeTestMapCacheEvent> events = new();

    internal IReadOnlyList<ScribeTestMapCacheEvent> Events => events.ToArray();

    internal ScribeTestMap GetOrDerive(
        RepositorySnapshot snapshot,
        Func<RepositorySnapshot, ScribeTestMap> derive)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(derive);
        var inputDigest = ComputeInputDigest(snapshot);
        if (TryLoad(inputDigest, out var cached))
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
            storage.Write(
                FileName(inputDigest),
                ScribeTestMapEnvelope.Create(inputDigest, environment, map).Write());
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

        // 投影摘要相等 ⟺ 两树之间无派生输入变更,这正是 EvaluateCapacity 现有 guard(A 层)跳过派生所依赖的同一不变量;本层不放宽也不收紧它。
        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    private bool TryLoad(string inputDigest, out ScribeTestMap map)
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

        if (!string.Equals(
                envelope.Environment.DotnetSdkVersion,
                environment.DotnetSdkVersion,
                StringComparison.Ordinal))
        {
            Record(inputDigest, "invalid:environment-dotnet-sdk-version");
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
