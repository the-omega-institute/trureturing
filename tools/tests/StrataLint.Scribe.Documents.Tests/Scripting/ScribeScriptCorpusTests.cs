using System.Collections.Immutable;
using System.Reflection;
using StrataLint.Scribe;
using StrataLint.Scribe.Documents;
using Xunit;
using Xunit.Abstractions;

namespace StrataLint.Scribe.Documents.Tests;

public sealed class ScribeScriptCorpusTests
{
    private readonly ITestOutputHelper output;

    public ScribeScriptCorpusTests(ITestOutputHelper output) => this.output = output;

    [Fact]
    public void ScriptPackMatchesAssemblyAndReusesEntireCorpus()
    {
        var root = FindRepositoryRoot();
        var directory = Directory.CreateTempSubdirectory("scribe-script-pack-");
        try
        {
            var type = typeof(ScribeResourcePack).Assembly.GetType("StrataLint.Scribe.ScribeResourceScriptPacker");
            Assert.NotNull(type);
            var write = type.GetMethod("Write", BindingFlags.Public | BindingFlags.Static)!;
            var firstPath = Path.Combine(directory.FullName, "first.zip");
            var secondPath = Path.Combine(directory.FullName, "second.zip");
            var firstResult = write.Invoke(null, [root, firstPath, null])!;
            var secondResult = write.Invoke(null, [root, secondPath, firstPath])!;
            T Get<T>(object result, string name) => Assert.IsType<T>(result.GetType().GetProperty(name)!.GetValue(result));
            Assert.Empty(Get<ImmutableArray<ScribeScriptFailure>>(firstResult, "Failures"));
            Assert.Empty(Get<ImmutableArray<ScribeScriptFailure>>(secondResult, "Failures"));
            var first = ScribeResourcePack.Open(firstPath);
            var second = ScribeResourcePack.Open(secondPath);
            var definitions = DocumentAssembly.Definitions;
            Assert.Equal(definitions.Length, first.Manifest.EntryCount);
            Assert.Equal(definitions.Length, Get<ImmutableArray<string>>(firstResult, "ExecutedPaths").Length);
            Assert.Empty(Get<ImmutableArray<string>>(firstResult, "ReusedPaths"));
            Assert.Empty(Get<ImmutableArray<string>>(secondResult, "ExecutedPaths"));
            Assert.Equal(definitions.Length, Get<ImmutableArray<string>>(secondResult, "ReusedPaths").Length);
            Assert.Equal(first.Manifest.TotalSha256, second.Manifest.TotalSha256);
            foreach (var definition in definitions)
                Assert.Equal(ScribeResourceCodec.Encode(definition),
                    first.EncodedBytes(definition.Document.Header.Gid.Value).ToArray());
            output.WriteLine($"script pack definitions={definitions.Length}; firstExecuted={Get<ImmutableArray<string>>(firstResult, "ExecutedPaths").Length}; secondExecuted=0; secondReused={definitions.Length}; firstSha256={first.Manifest.TotalSha256}; secondSha256={second.Manifest.TotalSha256}; firstFileBytes={new FileInfo(firstPath).Length}; secondFileBytes={new FileInfo(secondPath).Length}");
        }
        finally { directory.Delete(recursive: true); }
    }

    [Fact]
    public void EveryDocumentDefinitionMatchesItsScript()
    {
        var root = FindRepositoryRoot();
        var paths = Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'))
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        Assert.NotEmpty(paths);
        var results = ScribeScriptHost.ExecuteBatch(root, paths);
        Assert.Equal(paths, results.Select(static result => result.RelativePath).Order(StringComparer.Ordinal));
        var current = DocumentAssembly.Definitions.ToDictionary(
            static definition => definition.Document.Header.Gid.Value, StringComparer.Ordinal);
        var failures = results.Where(static result => !result.IsSuccess).ToArray();
        var mismatches = results.Where(static result => result.IsSuccess)
            .Where(result => !current.TryGetValue(result.Definition!.Document.Header.Gid.Value, out var definition)
                || !ScribeResourceCodec.Encode(result.Definition).AsSpan()
                    .SequenceEqual(ScribeResourceCodec.Encode(definition)))
            .ToArray();

        output.WriteLine($"corpus paths={paths.Length}; hostFailures={failures.Length}; mismatches={mismatches.Length}");
        Assert.True(failures.Length == 0, string.Join(Environment.NewLine, failures.Take(8)));
        Assert.True(mismatches.Length == 0, string.Join(Environment.NewLine,
            mismatches.Take(8).Select(static result => $"{result.RelativePath}: CanonicalContentMismatch")));
        Assert.Equal(DocumentAssembly.Definitions.Length, paths.Length);
    }

    private static string FindRepositoryRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory);
             directory is not null;
             directory = directory.Parent)
        {
            if (File.Exists(Path.Combine(directory.FullName, "global.json"))
                && Directory.Exists(Path.Combine(directory.FullName, "Blueprint")))
                return directory.FullName;
        }
        throw new DirectoryNotFoundException("repository root was not found");
    }
}
