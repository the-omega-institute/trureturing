using System.Collections.Immutable;
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
