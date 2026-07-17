using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ConservativeCorpusEvaluatorTests
{
    [Fact]
    public void ProductionEvaluatorReplaysEveryBaseTomlGoldenCase()
    {
        var root = FindRepositoryRoot();
        var source = TomlGoldenLoader.LoadRepository(root);
        var corpus = GoldenCorpusMaterializer.Materialize(root);

        var run = ConservativeCorpusEvaluator.Evaluate(
            corpus.CanonicalBytes.AsSpan(),
            "sha256:" + new string('a', 64));

        Assert.Equal(source.Cases.Count, run.Cases.Length);
        Assert.Equal(corpus.CaseIds, run.Cases.Select(static item => item.CaseId));
        Assert.Equal(6, run.ContractCases.Length);
        foreach (var testCase in source.Cases)
        {
            var actual = Assert.Single(run.Cases, item => item.CaseId == $"golden:{testCase.Name}");
            Assert.Equal(
                testCase.ExpectedDiagnostics.Count == 0
                    ? ConservativeDisposition.Admit
                    : ConservativeDisposition.Block,
                actual.Disposition);
            Assert.Equal(
                testCase.ExpectedDiagnostics
                    .Select(static item => $"SL-{item.RuleNumber:000}")
                    .Distinct(StringComparer.Ordinal)
                    .Order(StringComparer.Ordinal),
                actual.BlockingRules);
        }

        foreach (var testCase in source.Cases.Where(static item => item.ContractEpoch is not null))
        {
            var actual = Assert.Single(
                run.ContractCases,
                item => item.CaseId == $"contract:{testCase.Name}");
            Assert.Equal(
                testCase.ContractEpoch!.ExpectedFindingCodes,
                actual.FindingCodes.ToArray());
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
        Assert.All(run.ActiveRules, rule => Assert.Contains(rule, witnessed));
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
