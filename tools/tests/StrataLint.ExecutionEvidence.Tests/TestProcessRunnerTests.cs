using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using System.Xml.Linq;
using Xunit;

namespace StrataLint.ExecutionEvidence.Tests;

public sealed class TestProcessRunnerTests
{
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void InfrastructureSkipRemainsVisibleAlongsideBusinessFailure(bool sameRun)
    {
        using var results = new TemporaryDirectory();
        WriteRun(Path.Combine(results.Path, "first.trx"), guard: sameRun, failed: true);
        if (!sameRun) WriteRun(Path.Combine(results.Path, "second.trx"), guard: true, failed: false);

        var failure = Assert.Throws<InfrastructureUnresolvedException>(
            () => TestResultEvidence.Load(results.Path));

        Assert.Contains("INFRASTRUCTURE_UNRESOLVED count=1", failure.Message, StringComparison.Ordinal);
        Assert.Contains("Synthetic.Hung", failure.Message, StringComparison.Ordinal);
        Assert.Contains("Synthetic.Fails", failure.Message, StringComparison.Ordinal);
        Assert.Contains("business failure sentinel", failure.Message, StringComparison.Ordinal);
        Assert.Contains("TRX_VALIDATION_FAILED TRX run summary did not succeed", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void OrdinarySkipDoesNotBecomeInfrastructureFailure()
    {
        using var results = new TemporaryDirectory();
        WriteRun(Path.Combine(results.Path, "ordinary.trx"), guard: true, failed: false,
            skipReason: "ordinary platform skip");

        Assert.Equal(1, TestResultEvidence.Load(results.Path).Executed);
    }

    [Fact]
    public void InfrastructureSkipMakesTrxEvidenceFailClosed()
    {
        var resultsDirectory = Path.Combine(
            Path.GetDirectoryName(typeof(TestProcessRunnerTests).Assembly.Location)!,
            "Fixtures");

        var failure = Assert.Throws<InfrastructureUnresolvedException>(
            () => TestResultEvidence.Load(resultsDirectory));

        Assert.Contains("INFRASTRUCTURE_UNRESOLVED count=1", failure.Message, StringComparison.Ordinal);
        Assert.Contains("Synthetic.Hung", failure.Message, StringComparison.Ordinal);
    }

    private static void WriteRun(string path, bool guard, bool failed,
        string skipReason = "infrastructure-hang-guard expired for synthetic-command")
    {
        var cases = new List<(string Name, string Outcome, string? Message)>
        {
            ("Passes", "Passed", null),
        };
        if (guard) cases.Add(("Hung", "NotExecuted", skipReason));
        if (failed) cases.Add(("Fails", "Failed", "business failure sentinel"));
        new XDocument(new XElement("TestRun",
            new XElement("Results", cases.Select(test => new XElement("UnitTestResult",
                new XAttribute("testId", test.Name), new XAttribute("testName", "Synthetic." + test.Name),
                new XAttribute("outcome", test.Outcome), test.Message is null ? null
                    : new XElement("Output", new XElement("ErrorInfo", new XElement("Message", test.Message)))))),
            new XElement("TestDefinitions", cases.Select(test => new XElement("UnitTest",
                new XAttribute("id", test.Name), new XAttribute("storage", "Synthetic.dll"),
                new XElement("TestMethod", new XAttribute("className", "Synthetic"), new XAttribute("name", test.Name))))),
            new XElement("ResultSummary", new XAttribute("outcome", failed ? "Failed" : "Completed"),
                new XElement("Counters", new XAttribute("executed", failed ? 2 : 1),
                    new XAttribute("passed", 1), new XAttribute("failed", failed ? 1 : 0))))).Save(path);
    }
}
