using System.Text;

namespace StrataLint.Tests;

public sealed class ReportSupervisorDeadlineTests
{
    [Fact]
    public void OuterDeadlineBoundsRunningChildBeforeTheRelativeBudget()
    {
        using var fixture = new ReportSupervisorFixture();
        var result = fixture.RunWithEnvironment("ci-bootstrap", false, fixture.LongRunningWorker,
            fixture.ClockEnvironment, "STRATALINT_BUILD_TIMEOUT_SECONDS=60", "PREFLIGHT_DEADLINE_AT=2000000020");

        Assert.Equal(124, result.ExitCode);
        Assert.Contains("PREFLIGHT_BUDGET_EXHAUSTED owner=outer-deadline", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
        Assert.True(fixture.ClockReads < 60, "the injected clock reached the relative deadline");
    }

    [Theory]
    [InlineData("invalid")]
    [InlineData("-1")]
    [InlineData("999999999999999999999")]
    [InlineData("1999999999")]
    public void InvalidOrExpiredOuterDeadlineDoesNotStartWorker(string deadline)
    {
        using var fixture = new ReportSupervisorFixture();
        var result = fixture.RunWithEnvironment("ci-bootstrap", false, fixture.ScratchWriter,
            fixture.ClockEnvironment, "PREFLIGHT_DEADLINE_AT=" + deadline);

        Assert.Equal(2, result.ExitCode);
        Assert.False(File.Exists(fixture.ScratchRecord));
    }
}
