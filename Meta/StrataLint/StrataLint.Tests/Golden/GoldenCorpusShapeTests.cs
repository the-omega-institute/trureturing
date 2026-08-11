using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class GoldenCorpusShapeTests
{
    public const int ExpectedCaseCount = 121;

    [Fact]
    public void CorpusContainsEveryTomlCaseExactlyOnce()
    {
        var corpus = TomlGoldenLoader.LoadRepository(FindRepositoryRoot());

        Assert.Equal(4, corpus.Files.Count);
        Assert.Equal(ExpectedCaseCount, corpus.Cases.Count);
        Assert.Equal(6, corpus.Cases.Count(static item => item.ContractEpoch is not null));
        Assert.Equal(
            [
                "contract-candidate-plan-attempt",
                "contract-double-consumption",
                "contract-glob-scope",
                "contract-no-obligation-coverage",
                "contract-same-pr-declaration-and-shrink",
                "contract-scope-outside-delta",
            ],
            corpus.Cases.Where(static item => item.ContractEpoch is not null)
                .Select(static item => item.Name)
                .Order(StringComparer.Ordinal)
                .ToArray());
        Assert.Equal(
            corpus.Cases.Count,
            corpus.Cases.Select(static item => item.Name).Distinct(StringComparer.Ordinal).Count());
        Assert.All(corpus.Cases, static item => Assert.False(string.IsNullOrWhiteSpace(item.Name)));
        Assert.All(corpus.Files, static file =>
        {
            var bytes = File.ReadAllBytes(file.Path);
            Assert.False(bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble));
            Assert.DoesNotContain((byte)'\r', bytes);
            Assert.Equal((byte)'\n', bytes[^1]);
        });
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
