using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class GoldenCorpusTests
{
    private static readonly string RepositoryRoot = FindRepositoryRoot();
    private static readonly GoldenCorpusSet Corpus = TomlGoldenLoader.LoadRepository(RepositoryRoot);

    public static TheoryData<string> Cases
    {
        get
        {
            var data = new TheoryData<string>();
            foreach (var item in Corpus.Cases)
            {
                data.Add(item.Name);
            }

            return data;
        }
    }

    [Theory]
    [MemberData(nameof(Cases))]
    public void EveryTomlCaseMatchesCurrentEngineDiagnostics(string caseName)
    {
        var testCase = Corpus.Cases.Single(item => item.Name == caseName);
        var actual = GoldenCorpusMaterializer.Evaluate(RepositoryRoot, testCase)
            .Select(static item => item.Render())
            .Order(StringComparer.Ordinal)
            .ToArray();
        var expected = testCase.ExpectedDiagnostics
            .Select(static item =>
                $"{RuleId.CreateKnown(item.RuleNumber).Value} "
                + $"{RepoPath.CreateKnown(item.Path).Value}: {item.Message}")
            .Order(StringComparer.Ordinal)
            .ToArray();
        var expectedText = Render(expected);
        var actualText = Render(actual);

        Assert.Equal(expectedText, actualText);
        Assert.Equal(Encoding.UTF8.GetBytes(expectedText), Encoding.UTF8.GetBytes(actualText));
    }

    private static string Render(string[] diagnostics) =>
        string.Join('\n', diagnostics) + (diagnostics.Length == 0 ? string.Empty : "\n");

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
