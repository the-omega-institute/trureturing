using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class AtomContextCliFixture
{
    internal static ProductionCliEnvironment Environment(this AtomContextFixture fixture, string root = "/repo") => new(root,
        new FakeRepositoryGateway(RawChangeSet.Create([]), fixture.RawSnapshot(), null), new FakeLeanReportSource(null));
}
