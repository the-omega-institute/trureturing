using StrataLint.Engine;
using Xunit;

namespace StrataLint.Tests;

public sealed class TestProcessRunnerTests
{
    [Fact]
    public void HangGuardExpirationIsReportedAsInfrastructureSkip() =>
        TestProcessRunner.Classify(
            static () => throw new TimeoutException("synthetic timeout"),
            "synthetic-command");

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
