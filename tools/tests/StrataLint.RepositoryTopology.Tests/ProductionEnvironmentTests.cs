using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.RepositoryTopology.Tests;

public sealed class ProductionEnvironmentTests
{
    [Fact]
    public void SelfTestIsByteStableAcrossTwoPasses()
    {
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        var environment = new ProductionCliEnvironment(
            repositoryRoot,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var first = environment.SelfTest(Array.Empty<string>());
        var second = environment.SelfTest(Array.Empty<string>());

        Assert.True(first.Success, first.Error);
        Assert.True(second.Success, second.Error);
        Assert.Equal(first.Output, second.Output);
        Assert.Contains("SELFTEST PASS", first.Output, StringComparison.Ordinal);
        Assert.Contains("SL-032", first.Output, StringComparison.Ordinal);
        Assert.Contains("SL-033", first.Output, StringComparison.Ordinal);
        Assert.Contains("SL-034", first.Output, StringComparison.Ordinal);
    }
}
