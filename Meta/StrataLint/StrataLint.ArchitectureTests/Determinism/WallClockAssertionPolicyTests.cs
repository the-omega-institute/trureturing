namespace StrataLint.ArchitectureTests;

public sealed class WallClockAssertionPolicyTests
{
    [Fact]
    public void RepositoryTestAssertionsDoNotDependOnWallClockValues()
    {
        var findings = WallClockAssertionPolicy.InspectRepository(RepositoryLayout.FindRoot());

        Assert.True(
            findings.Count == 0,
            string.Join(Environment.NewLine, findings.Select(static finding => finding.Message)));
    }

    [Theory]
    [InlineData("Assert.True(Stopwatch.StartNew().Elapsed < budget);")]
    [InlineData("Assert.Equal(expected, DateTime.Now);")]
    [InlineData("Assert.NotEqual(expected, DateTime.UtcNow);")]
    [InlineData("Assert.True(Environment.TickCount > 0);")]
    [InlineData("Assert.True(Environment.TickCount64 > 0);")]
    [InlineData("Stopwatch clock = Stopwatch.StartNew(); var elapsed = clock.Elapsed; Assert.True(elapsed < budget);")]
    [InlineData("Stopwatch clock = Stopwatch.StartNew(); clock.Elapsed.Should().BeLessThan(budget);")]
    public void EachSupportedWallClockAssertionShapeIsRejected(string body)
    {
        var findings = WallClockAssertionPolicy.InspectSource(
            "Synthetic.Tests/WallClockTests.cs",
            $"class C {{ void M() {{ {body} }} }}");

        Assert.Single(findings);
    }

    [Fact]
    public void WallClockRunawayGuardOutsideAnAssertionIsAllowed()
    {
        const string source = "class C { void M() { var clock = Stopwatch.StartNew(); RunWithGuard(clock.Elapsed); Assert.True(completed); } }";

        Assert.Empty(WallClockAssertionPolicy.InspectSource("Synthetic.Tests/GuardTests.cs", source));
    }

    [Theory]
    [InlineData("class C { TimeSpan Value; void M() { var clock = Stopwatch.StartNew(); Value = clock.Elapsed; } }")]
    [InlineData("class C { TimeSpan M() { var clock = Stopwatch.StartNew(); return clock.Elapsed; } }")]
    [InlineData("class C { void M(ref TimeSpan value) { var clock = Stopwatch.StartNew(); value = clock.Elapsed; } }")]
    public void WallClockFlowsThatEscapeLocalAnalysisFailClosed(string source)
    {
        var finding = Assert.Single(WallClockAssertionPolicy.InspectSource(
            "Synthetic.Tests/UnsupportedFlowTests.cs",
            source));

        Assert.Contains("ASSUMED-UNVERIFIED", finding.Message, StringComparison.Ordinal);
    }
}
