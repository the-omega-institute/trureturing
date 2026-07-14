using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class GoldenCorpusMaterializerTests
{
    [Fact]
    public void MaterializerLoadsEveryCaseFromTheBaseTomlCorpusWithoutExpectedLabels()
    {
        var root = FindRepositoryRoot();
        var source = TomlGoldenLoader.LoadRepository(root);

        var corpus = GoldenCorpusMaterializer.Materialize(root);
        var canonical = Encoding.UTF8.GetString(corpus.CanonicalBytes.AsSpan());

        Assert.Equal(source.Cases.Count, corpus.CaseIds.Length);
        Assert.Equal(
            source.Cases.Select(static item => $"golden:{item.Name}").Order(StringComparer.Ordinal),
            corpus.CaseIds);
        Assert.DoesNotContain("expected", canonical, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void MaterializedCorpusRootAndBytesAreStable()
    {
        var root = FindRepositoryRoot();

        var first = GoldenCorpusMaterializer.Materialize(root);
        var second = GoldenCorpusMaterializer.Materialize(root);

        Assert.Equal(first.Root, second.Root);
        Assert.True(first.CanonicalBytes.AsSpan().SequenceEqual(second.CanonicalBytes.AsSpan()));
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
