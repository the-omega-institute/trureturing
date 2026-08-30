using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TestProcessRunnerClassificationTests
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
}
