namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void StartReturnsOnlyAfterReadyAndPublishesAStateAndStatusHandle()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.RunStart();

        Assert.Equal(0, result.ExitCode);
        Assert.StartsWith("state=", result.Output, StringComparison.Ordinal);
        Assert.Contains(" status_command=", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("pid=", result.Output, StringComparison.Ordinal);
        Assert.Single(result.Output.Split('\n', StringSplitOptions.RemoveEmptyEntries));
        Assert.Equal(0, fixture.RunStatus().ExitCode);
    }

    [Fact]
    public void MakePrWatchDelegatesToStartAndExposesStatusWithoutDuplicatingLogic()
    {
        var makefile = File.ReadAllText(Path.Combine(FindRepositoryRoot(), "Makefile"));

        Assert.Contains("pr-watch pr-watch-status", makefile, StringComparison.Ordinal);
        Assert.Contains(
            "make pr-watch-status                Report pr-watch alive/stalled/dead state",
            makefile,
            StringComparison.Ordinal);
        Assert.Contains(
            "Meta/StrataLint/scripts/pr-shepherd.sh start $(INTERVAL) $(CYCLES)",
            makefile,
            StringComparison.Ordinal);
        Assert.Contains(
            "pr-watch-status:\n\t@/bin/bash Meta/StrataLint/scripts/pr-shepherd.sh status",
            makefile,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "Meta/StrataLint/scripts/pr-shepherd.sh watch $(INTERVAL) $(CYCLES)",
            makefile,
            StringComparison.Ordinal);
    }
}
