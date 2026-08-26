using StrataLint.Engine;
using StrataLint.EngineeringScope;
using System.Text;

namespace StrataLint.Tests;

public sealed class TestProcessRunnerTests
{
    [Fact]
    public void SuccessfulProcessOutputIsReturnedWithoutReplacement()
    {
        var expected = new ProcessOutput(17, [1, 2, 3], [4, 5]);
        ProcessOutput? actual = null;

        var failure = Record.Exception(() => actual = TestProcessRunner.Classify(
            () => expected,
            "synthetic-command"));

        Assert.Null(failure);
        Assert.Same(expected, actual);
    }

    [Fact]
    public void NonTimeoutExceptionPropagatesWithoutReplacement()
    {
        var expected = new InvalidOperationException("synthetic failure");

        var actual = Record.Exception(() => TestProcessRunner.Classify(
            () => throw expected,
            "synthetic-command"));

        Assert.Same(expected, actual);
    }

    [Fact]
    public void HangGuardExpirationIsClassifiedAsSkip()
    {
        var exception = Assert.Throws<SkipException>(() =>
            TestProcessRunner.Classify(
                static () => throw new TimeoutException("synthetic timeout"),
                "synthetic-command"));

        Assert.Contains("infrastructure-hang-guard", exception.Message, StringComparison.Ordinal);
        Assert.Contains("synthetic-command", exception.Message, StringComparison.Ordinal);
        Assert.Contains("synthetic timeout", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void InfrastructureSkipMakesTrxEvidenceFailClosed()
    {
        using var temporary = new TemporaryDirectory();
        var trx = Path.Combine(temporary.Path, "synthetic.trx");
        File.WriteAllText(
            trx,
            """
            <?xml version="1.0" encoding="utf-8"?>
            <TestRun xmlns="http://microsoft.com/schemas/VisualStudio/TeamTest/2010">
              <Results>
                <UnitTestResult testId="test-id" testName="Synthetic.Hung" outcome="NotExecuted">
                  <Output><ErrorInfo><Message>infrastructure-hang-guard expired for synthetic-command</Message></ErrorInfo></Output>
                </UnitTestResult>
              </Results>
              <TestDefinitions>
                <UnitTest storage="Synthetic.dll" id="test-id">
                  <TestMethod className="Synthetic.Tests" name="Hung" />
                </UnitTest>
              </TestDefinitions>
              <ResultSummary><Counters executed="0" /></ResultSummary>
            </TestRun>
            """,
            new UTF8Encoding(false));

        var failure = Assert.Throws<InfrastructureUnresolvedException>(
            () => TestResultEvidence.Load(temporary.Path));

        Assert.Contains("INFRASTRUCTURE_UNRESOLVED count=1", failure.Message, StringComparison.Ordinal);
        Assert.Contains("Synthetic.Hung", failure.Message, StringComparison.Ordinal);
    }
}
