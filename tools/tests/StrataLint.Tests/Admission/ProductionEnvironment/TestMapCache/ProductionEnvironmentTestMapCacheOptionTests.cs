using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ProductionEnvironmentTestMapCacheOptionTests
{
    private const string Usage =
        "USAGE: StrataLint check [--protected-base REV] "
        + "[--test-map-cache-root DIR] --candidate-lean-report FILE";

    [Fact]
    public void CheckAcceptsTestMapCacheRoot()
    {
        var environment = EnvironmentWithUnreadableSnapshot();

        var outcome = environment.Check([
            "--test-map-cache-root", "/cache",
            "--candidate-lean-report", "candidate.json",
        ]);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.DoesNotContain("USAGE:", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckRejectsRepeatedTestMapCacheRoot()
    {
        var environment = EnvironmentWithUnreadableSnapshot();

        var outcome = environment.Check([
            "--test-map-cache-root", "/cache-a",
            "--test-map-cache-root", "/cache-b",
            "--candidate-lean-report", "candidate.json",
        ]);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Equal(Usage, failure.Message);
    }

    [Fact]
    public void CheckRejectsTestMapCacheRootWithoutValue()
    {
        var environment = EnvironmentWithUnreadableSnapshot();

        var outcome = environment.Check(["--test-map-cache-root"]);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Equal(Usage, failure.Message);
    }

    [Fact]
    public void CheckUsageNamesTestMapCacheRoot()
    {
        var environment = EnvironmentWithUnreadableSnapshot();

        var outcome = environment.Check(["--unknown", "value"]);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Equal(Usage, failure.Message);
    }

    private static ProductionCliEnvironment EnvironmentWithUnreadableSnapshot() =>
        new(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create([]),
                current: null,
                baseline: null),
            new FakeLeanReportSource(null));
}
