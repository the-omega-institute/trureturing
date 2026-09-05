using System.Collections.Concurrent;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

public sealed class ScribeTestMapStoreTests
{
    private static readonly ScribeTestMapEnvironment TestEnvironment =
        new("test-rid", ".NET test framework", "10.0.100-test");

    [Fact]
    public void InputDigestIgnoresNonDerivationInputs()
    {
        var before = Snapshot(("config/example.yaml", "before"), ("src/Test.cs", "class Test {}"));
        var after = Snapshot(("config/example.yaml", "after"), ("src/Test.cs", "class Test {}"));

        Assert.Equal(
            ScribeTestMapStore.ComputeInputDigest(before),
            ScribeTestMapStore.ComputeInputDigest(after));
    }

    [Theory]
    [InlineData("src/Test.cs")]
    [InlineData("src/Test.csproj")]
    [InlineData("eng/Directory.Build.props")]
    [InlineData("global.json")]
    public void InputDigestChangesWhenAnyDerivationInputChanges(string path)
    {
        var before = Snapshot((path, "before"), ("README.md", "same"));
        var after = Snapshot((path, "after"), ("README.md", "same"));

        Assert.NotEqual(
            ScribeTestMapStore.ComputeInputDigest(before),
            ScribeTestMapStore.ComputeInputDigest(after));
    }

    [Fact]
    public void InputDigestIgnoresProcessEnvironment()
    {
        var snapshot = Snapshot(("src/Test.cs", "class Test {}"));
        const string Variable = "STRATALINT_TEST_MAP_DIGEST_TEST";
        var original = Environment.GetEnvironmentVariable(Variable);
        try
        {
            Environment.SetEnvironmentVariable(Variable, "before");
            var before = ScribeTestMapStore.ComputeInputDigest(snapshot);
            Environment.SetEnvironmentVariable(Variable, "after");

            Assert.Equal(before, ScribeTestMapStore.ComputeInputDigest(snapshot));
        }
        finally
        {
            Environment.SetEnvironmentVariable(Variable, original);
        }
    }

    [Fact]
    public void HitDoesNotInvokeDerivation()
    {
        var snapshot = Snapshot(("src/Test.cs", "class Test {}"));
        var digest = ScribeTestMapStore.ComputeInputDigest(snapshot);
        var storage = new MemoryStorage();
        storage.Seed(digest + ".json", ScribeTestMapEnvelope.Create(
            digest,
            TestEnvironment,
            Map("cached")).Write());
        var store = new ScribeTestMapStore(storage, TestEnvironment);

        var result = store.GetOrDerive(
            snapshot,
            static _ => throw new InvalidOperationException("derivation must not run"));

        Assert.Equal("cached", Assert.Single(result.Methods).Id);
        Assert.Collection(store.Events, item => Assert.Equal("hit", item.Outcome));
    }

    [Fact]
    public void MissInvokesDerivationOnceAndStores()
    {
        var snapshot = Snapshot(("src/Test.cs", "class Test {}"));
        var storage = new MemoryStorage();
        var store = new ScribeTestMapStore(storage, TestEnvironment);
        var calls = 0;

        var result = store.GetOrDerive(snapshot, _ =>
        {
            Interlocked.Increment(ref calls);
            return Map("derived");
        });

        Assert.Equal("derived", Assert.Single(result.Methods).Id);
        Assert.Equal(1, calls);
        Assert.Equal(1, storage.WriteCount);
        Assert.Equal(["miss", "stored"], store.Events.Select(static item => item.Outcome));
    }

    [Theory]
    [InlineData("producer", "producer")]
    [InlineData("rid", "environment-rid")]
    [InlineData("framework", "environment-framework")]
    [InlineData("dotnet-sdk-version", "environment-dotnet-sdk-version")]
    [InlineData("digest", "input-digest")]
    [InlineData("corrupt-json", "invalid-json")]
    [InlineData("missing-field", "field")]
    public void InvalidEntryFailsClosedAndDerivesOnce(string mutation, string expectedReason)
    {
        var snapshot = Snapshot(("src/Test.cs", "class Test {}"));
        var digest = ScribeTestMapStore.ComputeInputDigest(snapshot);
        var storage = new MemoryStorage();
        storage.Seed(digest + ".json", InvalidBytes(mutation, digest));
        var store = new ScribeTestMapStore(storage, TestEnvironment);
        var calls = 0;

        var result = store.GetOrDerive(snapshot, _ =>
        {
            Interlocked.Increment(ref calls);
            return Map("derived");
        });

        Assert.Equal("derived", Assert.Single(result.Methods).Id);
        Assert.Equal(1, calls);
        Assert.Contains(
            store.Events,
            item => item.Outcome == "invalid:" + expectedReason);
    }

    [Fact]
    public void MapWithCompileFindingsIsNotStored()
    {
        var storage = new MemoryStorage();
        var store = new ScribeTestMapStore(storage, TestEnvironment);
        var map = new ScribeTestMap(
            [],
            [],
            [],
            [],
            [new MsBuildCompileFinding("src/Test.csproj", "query failed")]);

        var result = store.GetOrDerive(Snapshot(("src/Test.cs", "class Test {}")), _ => map);

        Assert.Same(map, result);
        Assert.Equal(0, storage.WriteCount);
        Assert.Contains(
            store.Events,
            static item => item.Outcome == "store-skipped-compile-findings");
    }

    [Fact]
    public void StorageWriteFailureDoesNotChangeReturnedMap()
    {
        var storage = new MemoryStorage { WriteFailure = new IOException("synthetic failure") };
        var store = new ScribeTestMapStore(storage, TestEnvironment);
        var map = Map("derived");

        var result = store.GetOrDerive(Snapshot(("src/Test.cs", "class Test {}")), _ => map);

        Assert.Same(map, result);
        Assert.Contains(
            store.Events,
            static item => item.Outcome.StartsWith("store-failed:", StringComparison.Ordinal));
    }

    [Fact]
    public void DirectoryStorageWritesAtomicallyAndCreatesRoot()
    {
        var parent = Directory.CreateTempSubdirectory("stratalint-test-map-storage").FullName;
        var root = Path.Combine(parent, "cache");
        var first = Encoding.UTF8.GetBytes(new string('a', 8_193));
        var second = Encoding.UTF8.GetBytes(new string('b', 12_289));
        try
        {
            var storage = new DirectoryScribeTestMapStorage(root);

            Parallel.Invoke(
                () => storage.Write("entry.json", first),
                () => storage.Write("entry.json", second));

            var bytes = TemporaryFileSystem.File.ReadAllBytes(Path.Combine(root, "entry.json"));
            Assert.True(bytes.SequenceEqual(first) || bytes.SequenceEqual(second));
            Assert.DoesNotContain(
                Directory.EnumerateFiles(root),
                static path => path.EndsWith(".tmp", StringComparison.Ordinal));
        }
        finally
        {
            Directory.Delete(parent, recursive: true);
        }
    }

    private static byte[] InvalidBytes(string mutation, string digest)
    {
        if (mutation == "corrupt-json")
        {
            return "{"u8.ToArray();
        }

        var envelopeDigest = mutation == "digest" ? new string('f', 64) : digest;
        var root = Assert.IsType<JsonObject>(JsonNode.Parse(Encoding.UTF8.GetString(
            ScribeTestMapEnvelope.Create(envelopeDigest, TestEnvironment, Map("cached")).Write())));
        switch (mutation)
        {
            case "producer": root["producer"]!["engine_mvid"] = new string('0', 32); break;
            case "rid": root["environment"]!["rid"] = "other-rid"; break;
            case "framework": root["environment"]!["framework"] = "other-framework"; break;
            case "dotnet-sdk-version": root["environment"]!["dotnet_sdk_version"] = "other-sdk"; break;
            case "digest": break;
            case "missing-field": root["map"]!.AsObject().Remove("methods"); break;
            default: throw new ArgumentOutOfRangeException(nameof(mutation));
        }

        return StructuredCanonicalWriter.WriteJson(
            JsonSerializer.SerializeToElement(root)).ToArray();
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files)
    {
        var raw = RawRepositorySnapshot.Create(
            files.Select(static file => RawRepositoryEntry.FromText(file.Path, file.Text)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static ScribeTestMap Map(string id) => new(
        [new ScribeTestMethod("partition", "src/Test.cs", id, [TestMapUnknownReason.Other])],
        [],
        [],
        [],
        []);

    private sealed class MemoryStorage : IScribeTestMapStorage
    {
        private readonly ConcurrentDictionary<string, byte[]> files = new(StringComparer.Ordinal);

        internal Exception? WriteFailure { get; init; }

        internal int WriteCount { get; private set; }

        public bool TryRead(string name, out byte[] bytes)
        {
            if (files.TryGetValue(name, out var stored))
            {
                bytes = stored.ToArray();
                return true;
            }

            bytes = [];
            return false;
        }

        public void Write(string name, byte[] bytes)
        {
            WriteCount++;
            if (WriteFailure is not null)
            {
                throw WriteFailure;
            }

            files[name] = bytes.ToArray();
        }

        internal void Seed(string name, byte[] bytes) => files[name] = bytes.ToArray();
    }

    private static class TemporaryFileSystem
    {
        internal static class File
        {
            internal static byte[] ReadAllBytes(string path) => System.IO.File.ReadAllBytes(path);
        }
    }
}
