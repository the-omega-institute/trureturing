using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void UpstreamVerbDispatchesClearThroughProductionEnvironmentWithoutLean()
    {
        using var f = new SettleUpstreamCommandTests.Fixture();
        Assert.True(f.Run().Success);
        var raw = f.Raw();
        var report = new FakeLeanReportSource(null);
        var environment = new ProductionCliEnvironment(f.Root,
            new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw), report);
        var console = new BufferedConsole();
        Assert.Equal(0, CliApplication.Run(["settle-upstream", "--clear", f.Id, "--base", "baseline"], environment, console));
        Assert.Contains("SETTLE_UPSTREAM_CLEARED", console.Output, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(f.Root, f.ProbePath)));
        Assert.Equal(0, report.CallCount);
        Assert.Equal(2, CliApplication.Run(["settle-upstream", "--clear", f.Id, "--base", "baseline"],
            new ProductionCliEnvironment(f.Root, new FakeRepositoryGateway(RawChangeSet.Create([]), f.Raw(), raw), report), new BufferedConsole()));
    }

    [Fact]
    public void UpstreamVerbReadsStrictRequestAndMapsFailuresToExitTwo()
    {
        using var f = new SettleUpstreamCommandTests.Fixture();
        var path = Path.Combine(f.Root, "request.toml");
        global::StrataLint.TestSupport.TemporaryFileSystem.File.WriteAllBytes(path, Encoding.UTF8.GetBytes(f.Request + "extra = 'x'\n"));
        var raw = f.Raw();
        var environment = new ProductionCliEnvironment(f.Root, new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw), new FakeLeanReportSource(null));
        var console = new BufferedConsole();
        Assert.Equal(2, CliApplication.Run(["settle-upstream", "--request", path, "--base", "baseline"], environment, console));
        Assert.StartsWith("SETTLE_UPSTREAM_INVALID REQUEST_KEYS_INVALID", console.Error, StringComparison.Ordinal);
    }
}
