using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ConservativeCorpusEvaluatorTests
{
    [Fact]
    public void ProductionEvaluatorReplaysEveryBaseTypedGoldenCase()
    {
        var corpus = GoldenCorpusMaterializer.Materialize(FindRepositoryRoot());

        var run = ConservativeCorpusEvaluator.Evaluate(
            corpus.CanonicalBytes.AsSpan(),
            "sha256:" + new string('a', 64));

        Assert.Equal(GoldenCorpus.All.Count, run.Cases.Length);
        Assert.Equal(corpus.CaseIds, run.Cases.Select(static item => item.CaseId));
        foreach (var source in GoldenCorpus.All)
        {
            var actual = Assert.Single(run.Cases, item => item.CaseId == $"golden:{source.Name}");
            Assert.Equal(
                source.ExpectedDiagnostics.Count == 0
                    ? ConservativeDisposition.Admit
                    : ConservativeDisposition.Block,
                actual.Disposition);
            Assert.Equal(
                source.ExpectedDiagnostics
                    .Select(static item => $"SL-{item.RuleNumber:000}")
                    .Distinct(StringComparer.Ordinal)
                    .Order(StringComparer.Ordinal),
                actual.BlockingRules);
        }
    }

    [Fact]
    public void BaseActualResultsProvideAFloorForEveryActiveBlockingRule()
    {
        var corpus = GoldenCorpusMaterializer.Materialize(FindRepositoryRoot());
        var run = ConservativeCorpusEvaluator.Evaluate(
            corpus.CanonicalBytes.AsSpan(),
            "sha256:" + new string('a', 64));

        var witnessed = run.Cases
            .SelectMany(static item => item.BlockingRules)
            .ToHashSet(StringComparer.Ordinal);
        Assert.All(
            run.ActiveRules.Where(static rule => rule != "SL-022"),
            rule => Assert.Contains(rule, witnessed));
    }

    [Fact]
    public void ObjectHashMismatchFailsClosed()
    {
        var corpus = GoldenCorpusMaterializer.Materialize(FindRepositoryRoot());
        var text = Encoding.UTF8.GetString(corpus.CanonicalBytes.AsSpan());
        const string marker = "\"bytes_base64\": \"";
        var index = text.IndexOf(marker, StringComparison.Ordinal) + marker.Length;
        Assert.True(index >= marker.Length);
        var replacement = text[index] == 'A' ? 'B' : 'A';
        var corrupted = text[..index] + replacement + text[(index + 1)..];

        var exception = Assert.Throws<FormatException>(() =>
            ConservativeCorpusEvaluator.Evaluate(
                Encoding.UTF8.GetBytes(corrupted),
                "sha256:" + new string('a', 64)));

        Assert.Contains("object root", exception.Message, StringComparison.OrdinalIgnoreCase);
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
