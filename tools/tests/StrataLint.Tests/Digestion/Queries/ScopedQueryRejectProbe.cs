using StrataLint.Cli;
using StrataLint.Engine;
using Xunit;
using static StrataLint.TestSupport.AtomContextFixture;

namespace StrataLint.Tests;

public sealed class ScopedQueryRejectProbe
{
    [Fact]
    public void InstalledContextRejectsItsSelectedMissingSource()
    {
        var fixture = Create();
        var raw = fixture.RawSnapshot(includeSource: false);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var result = new ProductionCliEnvironment("/repo", gateway, new FakeLeanReportSource(null))
            .AtomContext(["--atom-id", Id(fixture.Atomized.Claims[1]), "--source", "source"]);
        Assert.False(result.Success);
        Assert.StartsWith("ATOM_CONTEXT_INVALID SOURCE_MISSING ", result.Error, StringComparison.Ordinal);
        Assert.Empty(result.Output);
        Assert.Equal(0, gateway.WholeTreeReadCount);
    }
}
