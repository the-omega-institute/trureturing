using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class GoldenCorpusTests
{
    public static TheoryData<string> Cases
    {
        get
        {
            var data = new TheoryData<string>();
            foreach (var item in GoldenCorpus.All)
            {
                data.Add(item.Name);
            }

            return data;
        }
    }

    [Theory]
    [MemberData(nameof(Cases))]
    public void EveryTypedCaseMatchesCurrentEngineDiagnostics(string caseName)
    {
        var testCase = GoldenCorpus.All.Single(item => item.Name == caseName);
        var fixture = new RuleFixture();
        fixture.NormalizeGoldenBackfillTargets();
        fixture.ApplyGoldenMutations(caseName, testCase.BaselineMutations, baseline: true);
        fixture.ApplyGoldenMutations(caseName, testCase.BaselineMutations, baseline: false);
        fixture.ApplyGoldenMutations(caseName, testCase.Mutations, baseline: false);

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.BuildGoldenContext(testCase.Changes)));
        var actual = completed.Capability.Diagnostics
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
}
