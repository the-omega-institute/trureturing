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
        new("test-rid", ".NET test framework", "/test/dotnet", "10.0.100-test", new string('d', 64));

    [Fact]
    public void DescribeEnvironmentProbesResolvedDotnetHost()
    {
        var hosts = new List<string>();
        var environment = MsBuildCompileOracle.DescribeEnvironment(
            () => "/selected/dotnet",
            run: (host, arguments, directory, timeout, maximumOutputBytes, standardInput, environment) =>
            {
                hosts.Add(host);
                Assert.Equal(["--version"], arguments);
                Assert.NotNull(environment);
                Assert.Equal(MsBuildCompileOracle.EvaluationEnvironment(), environment);
                return new ProcessOutput(0, " 10.0.100-test\n"u8.ToArray(), []);
            });

        Assert.Equal(["/selected/dotnet"], hosts);
        Assert.Equal("/selected/dotnet", environment.DotnetHost);
        Assert.Equal("10.0.100-test", environment.DotnetSdkVersion);
        Assert.Equal(System.Runtime.InteropServices.RuntimeInformation.RuntimeIdentifier, environment.Rid);
        Assert.Equal(System.Runtime.InteropServices.RuntimeInformation.FrameworkDescription, environment.Framework);
        Assert.Equal(64, environment.EvaluationEnvironmentDigest.Length);
    }

    [Fact]
    public void ResolveDotnetExecutableUsesExplicitHostPath()
    {
        using var temporary = new TemporaryDirectory();
        var host = Path.Combine(temporary.Path, "selected-dotnet");
        TemporaryFileSystem.File.WriteAllText(host, "synthetic host; never executed");
        var original = Environment.GetEnvironmentVariable("DOTNET_HOST_PATH");
        try
        {
            Environment.SetEnvironmentVariable("DOTNET_HOST_PATH", host);
            Assert.Equal(host, MsBuildCompileOracle.ResolveDotnetExecutable());
        }
        finally
        {
            Environment.SetEnvironmentVariable("DOTNET_HOST_PATH", original);
        }
    }

    [Fact]
    public void QueryUsesEvaluationEnvironment()
    {
        using var temporary = new TemporaryDirectory();
        var expected = MsBuildCompileOracle.EvaluationEnvironment();
        var calls = 0;
        var result = MsBuildCompileOracle.Query(temporary.Path, ["Test.csproj"], "/fake/dotnet",
            run: (host, arguments, directory, timeout, maximumOutputBytes, standardInput, environment) =>
            {
                calls++;
                Assert.Equal("/fake/dotnet", host);
                Assert.Equal(temporary.Path, directory);
                Assert.Contains("-getItem:Compile", arguments);
                Assert.NotNull(environment);
                Assert.Equal(expected, environment);
                return new ProcessOutput(0, "{\"Items\":{\"Compile\":[]}}"u8.ToArray(), []);
            });

        Assert.Equal(1, calls);
        Assert.Empty(result.Findings);
    }

    [Fact]
    public void EvaluationEnvironmentIsAllowlistedOrderedAndImmutable()
    {
        var expected = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var name in new[] { "PATH", "HOME", "TMPDIR", "TMP", "TEMP", "DOTNET_ROOT",
                     "DOTNET_HOST_PATH", "NUGET_PACKAGES", "LANG", "LC_ALL" })
        {
            if (Environment.GetEnvironmentVariable(name) is { } value) expected.Add(name, value);
        }
        expected.Add("DOTNET_CLI_TELEMETRY_OPTOUT", "1");
        expected.Add("DOTNET_NOLOGO", "1");
        expected.Add("DOTNET_SKIP_FIRST_TIME_EXPERIENCE", "1");

        var actual = MsBuildCompileOracle.EvaluationEnvironment();

        Assert.Equal(expected.ToArray(), actual.ToArray());
        Assert.IsAssignableFrom<System.Collections.Immutable.IImmutableDictionary<string, string>>(actual);
    }

    [Fact]
    public void DescribeEnvironmentBindsEvaluationEnvironmentValues()
    {
        var original = Environment.GetEnvironmentVariable("LANG");
        try
        {
            Environment.SetEnvironmentVariable("LANG", "C");
            var before = MsBuildCompileOracle.DescribeEnvironment(
                () => "/fake/dotnet", _ => new ProcessOutput(0, "10.0.100-test"u8.ToArray(), []));
            Environment.SetEnvironmentVariable("LANG", "en_US.UTF-8");
            var after = MsBuildCompileOracle.DescribeEnvironment(
                () => "/fake/dotnet", _ => new ProcessOutput(0, "10.0.100-test"u8.ToArray(), []));

            Assert.NotEqual(before.EvaluationEnvironmentDigest, after.EvaluationEnvironmentDigest);
            Assert.Equal(before with { EvaluationEnvironmentDigest = after.EvaluationEnvironmentDigest }, after);
        }
        finally
        {
            Environment.SetEnvironmentVariable("LANG", original);
        }
    }

    [Fact]
    public void EvaluationEnvironmentDigestMismatchInvalidatesAndDerivesOnce()
    {
        var snapshot = Snapshot(("src/Test.cs", "class Test {}"));
        var storage = new MemoryStorage();
        var first = TestEnvironment with { EvaluationEnvironmentDigest = new string('a', 64) };
        var second = first with { EvaluationEnvironmentDigest = new string('b', 64) };
        new ScribeTestMapStore(storage, first, _ => Map("cached")).GetOrDerive(snapshot);
        var calls = 0;
        var store = new ScribeTestMapStore(storage, second, _ =>
        {
            calls++;
            return Map("fresh");
        });
        var result = store.GetOrDerive(snapshot);

        Assert.Equal(1, calls);
        Assert.Equal("fresh", Assert.Single(result.Methods).Id);
        Assert.Equal(["invalid:environment-evaluation-environment-digest", "stored"],
            store.Events.Select(static item => item.Outcome));
    }

    [Fact]
    public void ResolveUsesDescribedInputPaths()
    {
        var project = new ScribeCompilationProject("Test.csproj", "<Project />", "", [], [], null);
        var calls = 0;
        string[] assemblies = [typeof(object).Assembly.Location, typeof(ScribeTestMapStoreTests).Assembly.Location];

        var resolution = ScribeMetadataReferenceResolver.Resolve(project, projects =>
        {
            calls++;
            Assert.Same(project, Assert.Single(projects));
            return [.. assemblies, "/synthetic/package.nuspec"];
        });

        Assert.Equal(1, calls);
        Assert.Equal(assemblies, resolution.References.Select(static reference => reference.Display));
        Assert.Null(resolution.Degradation);
    }

    [Fact]
    public void SnapshotDerivationKeyChangesWhenMetadataDigestChanges()
    {
        using var temporary = new TemporaryDirectory();
        var path = Path.Combine(temporary.Path, "asset.dll");
        var snapshot = Snapshot(("src/Test.cs", "class Test {}"));
        TemporaryFileSystem.File.WriteAllText(path, "before");
        var before = ScribeTestMapDeriver.SnapshotDerivationKey(snapshot, _ => [path]);
        TemporaryFileSystem.File.WriteAllText(path, "after");

        Assert.NotEqual(before, ScribeTestMapDeriver.SnapshotDerivationKey(snapshot, _ => [path]));
    }

    [Fact]
    public void SnapshotDerivationIsNotMemoizedWhenMetadataChangesDuringDerivation()
    {
        var snapshot = Snapshot(("src/MetadataChangesDuringDerivation.cs", "class Test {}"));
        var descriptions = 0;
        IReadOnlyList<string> Describe(IEnumerable<ScribeCompilationProject> _) =>
            ++descriptions == 1 ? [] : [typeof(object).Assembly.Location];

        var calls = 0;
        ScribeTestMap Derive(RepositorySnapshot input)
        {
            Assert.Same(snapshot, input);
            calls++;
            return Map("synthetic");
        }
        var first = ScribeTestMapDeriver.DeriveSnapshot(snapshot, Describe, Derive);
        descriptions = 0;
        var second = ScribeTestMapDeriver.DeriveSnapshot(snapshot, Describe, Derive);

        Assert.Equal(2, calls);
        Assert.NotSame(first, second);
        Assert.Empty(first.CompileQueryFindings);
        Assert.Empty(second.CompileQueryFindings);
    }

    [Fact]
    public void MetadataChangedDuringDerivationSkipsStore()
    {
        var snapshot = Snapshot(("src/Test.cs", "class Test {}"));
        IReadOnlyList<string> paths = [];
        var storage = new MemoryStorage();
        var calls = 0;
        var store = new ScribeTestMapStore(storage, TestEnvironment, _ =>
        {
            calls++;
            paths = [typeof(object).Assembly.Location];
            return Map("derived-before-metadata-change");
        }, _ => paths);
        var result = store.GetOrDerive(snapshot);

        Assert.Equal(1, calls);
        Assert.Equal("derived-before-metadata-change", Assert.Single(result.Methods).Id);
        Assert.Equal(0, storage.WriteCount);
        Assert.Equal(["miss", "store-skipped-metadata-changed"],
            store.Events.Select(static item => item.Outcome));
    }

    [Theory]
    [InlineData(1, "version")]
    [InlineData(0, " \n")]
    public void DescribeEnvironmentRejectsFailedOrEmptyVersionProbe(int exitCode, string version)
    {
        Assert.Throws<InvalidOperationException>(() => MsBuildCompileOracle.DescribeEnvironment(
            () => "/selected/dotnet",
            _ => new ProcessOutput(exitCode, Encoding.UTF8.GetBytes(version), [])));
    }

    [Theory]
    [InlineData("asset.dll")]
    [InlineData("package.nuspec")]
    public void MetadataDigestChangesWhenAReferencedFileChanges(string name)
    {
        using var temporary = new TemporaryDirectory();
        var path = Path.Combine(temporary.Path, name);
        var snapshot = Snapshot(
            ("src/Test.csproj", "<Project />"),
            ("src/packages.lock.json", "{\"dependencies\":{}}"));
        IReadOnlyList<string> Inputs(IEnumerable<ScribeCompilationProject> projects)
        {
            var project = Assert.Single(projects);
            Assert.Equal("src/Test.csproj", project.Path);
            Assert.Equal("<Project />", project.ProjectContent);
            Assert.Equal("{\"dependencies\":{}}", project.PackageLockContent);
            return [path];
        }
        TemporaryFileSystem.File.WriteAllText(path, "before");
        var before = ScribeTestMapStore.ComputeMetadataDigest(snapshot, Inputs);
        var storage = new MemoryStorage();
        var store = new ScribeTestMapStore(storage, TestEnvironment, _ => Map("cached"), Inputs);
        store.GetOrDerive(snapshot);
        TemporaryFileSystem.File.WriteAllText(path, "after");

        Assert.NotEqual(before, ScribeTestMapStore.ComputeMetadataDigest(snapshot, Inputs));
        var calls = 0;
        var changedStore = new ScribeTestMapStore(storage, TestEnvironment, _ =>
        {
            calls++;
            return Map("changed");
        }, Inputs);
        var result = changedStore.GetOrDerive(snapshot);

        Assert.Equal(1, calls);
        Assert.Equal("changed", Assert.Single(result.Methods).Id);
        Assert.Contains(changedStore.Events, static item => item.Outcome == "invalid:metadata-digest");
        var hit = new ScribeTestMapStore(storage, TestEnvironment,
            _ => throw new InvalidOperationException("updated metadata must hit"), Inputs).GetOrDerive(snapshot);
        Assert.Equal("changed", Assert.Single(hit.Methods).Id);
        TemporaryFileSystem.File.Delete(path);
        Assert.NotEqual(before, ScribeTestMapStore.ComputeMetadataDigest(snapshot, Inputs));
    }

    [Fact]
    public void DescribeInputPathsIsSortedAndDeduplicated()
    {
        using var temporary = new TemporaryDirectory();
        string PackageDirectory(string id, string version) => Path.Combine(temporary.Path, id, version);
        var first = PackageDirectory("first", "1.0.0");
        var second = PackageDirectory("second", "2.0.0");
        var firstAsset = Path.Combine(first, "ref", "net10.0", "First.dll");
        var secondAsset = Path.Combine(second, "lib", "net10.0", "Second.dll");
        var firstNuspec = Path.Combine(first, "first.nuspec");
        var secondNuspec = Path.Combine(second, "second.nuspec");
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(firstAsset)!);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(secondAsset)!);
        TemporaryFileSystem.File.WriteAllText(firstAsset, "first assembly");
        TemporaryFileSystem.File.WriteAllText(secondAsset, "second assembly");
        TemporaryFileSystem.File.WriteAllText(firstNuspec,
            "<package><metadata><dependencies><dependency id=\"second\" version=\"2.0.0\" /></dependencies></metadata></package>");
        TemporaryFileSystem.File.WriteAllText(secondNuspec, "<package />");
        var project = new ScribeCompilationProject("Test.csproj",
            "<Project><ItemGroup><PackageReference Include=\"first\" Version=\"1.0.0\" /></ItemGroup></Project>",
            "", [], [], null);

        var paths = ScribeMetadataReferenceResolver.DescribeInputPaths([project, project], PackageDirectory);

        Assert.Equal(paths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal), paths);
        Assert.All(paths, static path => Assert.True(Path.IsPathFullyQualified(path)));
        Assert.Contains(typeof(object).Assembly.Location, paths);
        Assert.Equal(new[] { firstAsset, secondAsset, firstNuspec, secondNuspec }.Order(StringComparer.Ordinal),
            paths.Where(path => path.StartsWith(temporary.Path, StringComparison.Ordinal)));
    }

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
            ScribeTestMapStore.ComputeMetadataDigest(snapshot),
            TestEnvironment,
            Map("cached")).Write());
        var store = new ScribeTestMapStore(storage, TestEnvironment,
            static _ => throw new InvalidOperationException("derivation must not run"));
        var result = store.GetOrDerive(snapshot);

        Assert.Equal("cached", Assert.Single(result.Methods).Id);
        Assert.Collection(store.Events, item => Assert.Equal("hit", item.Outcome));
    }

    [Fact]
    public void MissInvokesDerivationOnceAndStores()
    {
        var snapshot = Snapshot(("src/Test.cs", "class Test {}"));
        var storage = new MemoryStorage();
        var calls = 0;
        var store = new ScribeTestMapStore(storage, TestEnvironment, _ =>
        {
            Interlocked.Increment(ref calls);
            return Map("derived");
        });
        var result = store.GetOrDerive(snapshot);

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
    [InlineData("dotnet_host", "environment-dotnet-host")]
    [InlineData("evaluation-environment-digest", "environment-evaluation-environment-digest")]
    [InlineData("metadata-digest", "metadata-digest")]
    [InlineData("digest", "input-digest")]
    [InlineData("corrupt-json", "invalid-json")]
    [InlineData("missing-field", "field")]
    public void InvalidEntryFailsClosedAndDerivesOnce(string mutation, string expectedReason)
    {
        var snapshot = Snapshot(("src/Test.cs", "class Test {}"));
        var digest = ScribeTestMapStore.ComputeInputDigest(snapshot);
        var storage = new MemoryStorage();
        storage.Seed(digest + ".json", InvalidBytes(mutation, digest,
            ScribeTestMapStore.ComputeMetadataDigest(snapshot)));
        var calls = 0;
        var store = new ScribeTestMapStore(storage, TestEnvironment, _ =>
        {
            Interlocked.Increment(ref calls);
            return Map("derived");
        });
        var result = store.GetOrDerive(snapshot);

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
        var map = new ScribeTestMap(
            [],
            [],
            [],
            [],
            [new MsBuildCompileFinding("src/Test.csproj", "query failed")]);

        var store = new ScribeTestMapStore(storage, TestEnvironment, _ => map);
        var result = store.GetOrDerive(Snapshot(("src/Test.cs", "class Test {}")));

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
        var map = Map("derived");
        var store = new ScribeTestMapStore(storage, TestEnvironment, _ => map);
        var result = store.GetOrDerive(Snapshot(("src/Test.cs", "class Test {}")));

        Assert.Same(map, result);
        Assert.Contains(
            store.Events,
            static item => item.Outcome.StartsWith("store-failed:", StringComparison.Ordinal));
    }

    [Fact]
    public void DirectoryStorageWritesAtomicallyAndCreatesRoot()
    {
        using var root = new TemporaryDirectory();
        var cacheRoot = Path.Combine(root.Path, "cache");
        var first = Encoding.UTF8.GetBytes(new string('a', 8_193));
        var second = Encoding.UTF8.GetBytes(new string('b', 12_289));
        var storage = new DirectoryScribeTestMapStorage(cacheRoot);

        Parallel.Invoke(
            () => storage.Write("entry.json", first),
            () => storage.Write("entry.json", second));

        var bytes = TemporaryFileSystem.File.ReadAllBytes(Path.Combine(cacheRoot, "entry.json"));
        Assert.True(bytes.SequenceEqual(first) || bytes.SequenceEqual(second));
        Assert.DoesNotContain(
            TemporaryFileSystem.Directory.EnumerateFiles(root),
            static path => path.EndsWith(".tmp", StringComparison.Ordinal));
    }

    private static byte[] InvalidBytes(string mutation, string digest, string metadataDigest)
    {
        if (mutation == "corrupt-json")
        {
            return "{"u8.ToArray();
        }

        var envelopeDigest = mutation == "digest" ? new string('f', 64) : digest;
        var root = Assert.IsType<JsonObject>(JsonNode.Parse(Encoding.UTF8.GetString(
            ScribeTestMapEnvelope.Create(envelopeDigest, metadataDigest, TestEnvironment, Map("cached")).Write())));
        switch (mutation)
        {
            case "producer": root["producer"]!["engine_mvid"] = new string('0', 32); break;
            case "rid": root["environment"]!["rid"] = "other-rid"; break;
            case "framework": root["environment"]!["framework"] = "other-framework"; break;
            case "dotnet-sdk-version": root["environment"]!["dotnet_sdk_version"] = "other-sdk"; break;
            case "dotnet_host": root["environment"]!["dotnet_host"] = "/other/dotnet"; break;
            case "evaluation-environment-digest": root["environment"]!["evaluation_environment_digest"] = new string('e', 64); break;
            case "metadata-digest": root["metadata_digest"] = new string('e', 64); break;
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
        internal static class Directory
        {
            internal static void CreateDirectory(string path) => System.IO.Directory.CreateDirectory(path);

            internal static IEnumerable<string> EnumerateFiles(TemporaryDirectory root) =>
                System.IO.Directory.EnumerateFiles(root.Path, "*", SearchOption.AllDirectories);
        }

        internal static class File
        {
            internal static void WriteAllText(string path, string text) => System.IO.File.WriteAllText(path, text);

            internal static void Delete(string path) => System.IO.File.Delete(path);

            internal static byte[] ReadAllBytes(string path) =>
                StrataLint.TestSupport.TemporaryFileSystem.File.ReadAllBytes(path);
        }
    }
}
