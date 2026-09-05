using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ProductionEnvironmentTestMapCacheOptionTests
{
    private const string Usage =
        "USAGE: StrataLint check [--protected-base REV] "
        + "[--test-map-cache-root DIR] --candidate-lean-report FILE";

    [Fact]
    public void CheckUsesStoreWhenCacheRootCanBeCreated()
    {
        using var temporary = new TemporaryDirectory();
        using var error = new StringWriter();
        var descriptions = 0;
        ScribeTestMapEnvironment Describe()
        {
            descriptions++;
            return DescribeFixedEnvironment();
        }
        var (environment, report) = EnvironmentWithCheckFixture(temporary.Path, error, Describe);
        var root = Path.Combine(temporary.Path, "cache");
        var console = new BufferedConsole();

        var code = CliApplication.Run([
            "check", "--candidate-lean-report", report, "--test-map-cache-root", root,
        ], environment, console);

        Assert.True(code != 2, console.Error);
        Assert.Contains("stored", CacheOutcomes(error.ToString()));
        var firstCode = code;
        error.GetStringBuilder().Clear();
        code = CliApplication.Run([
            "check", "--candidate-lean-report", report, "--test-map-cache-root", root,
        ], environment, new BufferedConsole());
        Assert.Equal(firstCode, code);
        Assert.Contains("hit", CacheOutcomes(error.ToString()));
        Assert.Equal(2, descriptions);
    }

    [Theory]
    [InlineData("host")]
    [InlineData("exit")]
    [InlineData("empty")]
    public void CheckDisablesCacheWhenHostOrVersionProbeFailsWithoutChangingExitCode(string failure)
    {
        using var temporary = new TemporaryDirectory();
        using var error = new StringWriter();
        var probes = 0;
        var spawnAttempts = 0;
        ScribeTestMapEnvironment Describe()
        {
            probes++;
            return MsBuildCompileOracle.DescribeEnvironment(
                () => failure == "host" ? throw new IOException("host resolution failed") : "/selected/dotnet",
                _ => new ProcessOutput(failure == "exit" ? 7 : 0, " \n"u8.ToArray(), []),
                run: (host, arguments, directory, timeout, maximumOutputBytes, standardInput, environment) =>
                {
                    spawnAttempts++;
                    throw new InvalidOperationException("process runner must not be called");
                });
        }
        var (environment, report) = EnvironmentWithCheckFixture(temporary.Path, error, Describe);
        var expected = CliApplication.Run(["check", "--candidate-lean-report", report],
            environment, new BufferedConsole());

        var actual = CliApplication.Run([
            "check", "--candidate-lean-report", report,
            "--test-map-cache-root", Path.Combine(temporary.Path, "cache"),
        ], environment, new BufferedConsole());

        Assert.Equal(expected, actual);
        Assert.NotEqual(2, actual);
        Assert.Equal(1, probes);
        Assert.Equal(0, spawnAttempts);
        Assert.Equal("disabled:dotnet-version-" + (failure == "host" ? "IOException" : "InvalidOperationException"),
            Assert.Single(CacheOutcomes(error.ToString())));
    }

    [Fact]
    public void CheckCacheEventWriteFailureDoesNotChangeDecision()
    {
        using var temporary = new TemporaryDirectory();
        using var error = new FailingEventWriter();
        var descriptions = 0;
        ScribeTestMapEnvironment Describe()
        {
            descriptions++;
            return DescribeFixedEnvironment();
        }
        var (environment, report) = EnvironmentWithCheckFixture(temporary.Path, error, Describe);
        var expectedConsole = new BufferedConsole();
        var expected = CliApplication.Run(["check", "--candidate-lean-report", report],
            environment, expectedConsole);
        var actualConsole = new BufferedConsole();

        var actual = CliApplication.Run([
            "check", "--candidate-lean-report", report,
            "--test-map-cache-root", Path.Combine(temporary.Path, "cache"),
        ], environment, actualConsole);

        Assert.True(error.Attempts > 0);
        Assert.NotEqual(2, actual);
        Assert.Equal(expected, actual);
        Assert.Equal(expectedConsole.Output, actualConsole.Output);
        Assert.Equal(expectedConsole.Error, actualConsole.Error);
        Assert.Equal(1, descriptions);
    }

    [Fact]
    public void CheckReportsCacheRootConstructionFailureWithoutProbingEnvironment()
    {
        using var temporary = new TemporaryDirectory();
        using var error = new StringWriter();
        var probes = 0;
        ScribeTestMapEnvironment Describe()
        {
            probes++;
            return DescribeFixedEnvironment();
        }
        var (environment, report) = EnvironmentWithCheckFixture(temporary.Path, error, Describe);
        var expected = CliApplication.Run(["check", "--candidate-lean-report", report],
            environment, new BufferedConsole());

        var actual = CliApplication.Run([
            "check", "--candidate-lean-report", report, "--test-map-cache-root", "\0",
        ], environment, new BufferedConsole());

        Assert.Equal(expected, actual);
        Assert.NotEqual(2, actual);
        Assert.Equal(0, probes);
        Assert.Equal("disabled:cache-root-ArgumentException", Assert.Single(CacheOutcomes(error.ToString())));
    }

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
    public void CheckRejectsEmptyTestMapCacheRoot()
    {
        var environment = EnvironmentWithUnreadableSnapshot();

        var outcome = environment.Check([
            "--test-map-cache-root", "",
            "--candidate-lean-report", "candidate.json",
        ]);

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

    private static (ProductionCliEnvironment Environment, string Report) EnvironmentWithCheckFixture(
        string root, TextWriter error, Func<ScribeTestMapEnvironment> describe)
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        ProductionEnvironmentTests.InstallDefaultAdmissionPlaneFileMap(fixture);
        const string path = "tools/StrataLint.Engine/CacheChange.cs";
        fixture.Files[path] = "// synthetic cache change\n";
        var current = RawRepositorySnapshot.Create(fixture.Files.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var baseline = RawRepositorySnapshot.Create(fixture.Baseline.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var report = Path.Combine(root, "candidate.json");
        RawLeanReportArtifact.WriteFile(report,
            Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(current)).Snapshot,
            LeanAxiomReport.Create(fixture.Reports));
        var environment = new ProductionCliEnvironment(root,
            new FakeRepositoryGateway(RawChangeSet.Create([path]), current, baseline),
            new FakeLeanReportSource(null))
        {
            TestMapCacheError = error,
            DescribeTestMapEnvironment = describe,
        };
        // Assert the injected factory before any CLI path can reach the production process probe.
        Assert.Equal(describe, environment.DescribeTestMapEnvironment);
        var console = new BufferedConsole();
        var code = CliApplication.Run(["check", "--candidate-lean-report", report], environment, console);
        Assert.True(code != 2, console.Error);
        return (environment, report);
    }

    private static ScribeTestMapEnvironment DescribeFixedEnvironment() =>
        new("test-rid", ".NET test framework", "/test/dotnet", "10.0.100-test", new string('d', 64));

    private static string[] CacheOutcomes(string output) => output
        .Split('\n', StringSplitOptions.RemoveEmptyEntries)
        .Select(static line =>
        {
            using var document = JsonDocument.Parse(line);
            Assert.Equal("test_map_cache", document.RootElement.GetProperty("event").GetString());
            Assert.Equal("admission-check", document.RootElement.GetProperty("scope").GetString());
            return document.RootElement.GetProperty("outcome").GetString()!;
        }).ToArray();

    private sealed class FailingEventWriter : TextWriter
    {
        public override Encoding Encoding => Encoding.UTF8;
        internal int Attempts { get; private set; }
        public override void WriteLine(string? value)
        {
            Attempts++;
            throw new IOException("event stream unavailable");
        }
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
