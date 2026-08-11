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

    [Fact]
    public void RepositoryTestProjectSetMatchesTheClosedScanScope()
    {
        var root = RepositoryLayout.FindRoot();
        var actual = GitIndexRepositoryFiles.Enumerate(root)
            .Select(static file => file.RelativePath)
            .Where(static path => path.EndsWith("Tests.csproj", StringComparison.Ordinal))
            .Select(static path => path[..(path.LastIndexOf('/') + 1)])
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(
            WallClockAssertionPolicy.TestProjectPrefixes.Order(StringComparer.Ordinal),
            actual);
    }

    [Theory]
    [InlineData("Assert.True(Stopwatch.StartNew().Elapsed < budget);")]
    [InlineData("Assert.Equal(expected, DateTime.Now);")]
    [InlineData("Assert.NotEqual(expected, DateTime.UtcNow);")]
    [InlineData("Assert.True(Environment.TickCount > 0);")]
    [InlineData("Assert.True(Environment.TickCount64 > 0);")]
    [InlineData("Assert.Equal(expected, DateTimeOffset.Now);")]
    [InlineData("Assert.Equal(expected, DateTimeOffset.UtcNow);")]
    [InlineData("Xunit.Assert.True(Stopwatch.StartNew().Elapsed < budget);")]
    [InlineData("global::Xunit.Assert.True(Stopwatch.StartNew().Elapsed < budget);")]
    [InlineData("ClassicAssert.True(Stopwatch.StartNew().Elapsed < budget);")]
    [InlineData("using ClockAssert = Xunit.Assert; class C { void M() { ClockAssert.True(Stopwatch.StartNew().Elapsed < budget); } }")]
    [InlineData("Stopwatch clock = Stopwatch.StartNew(); var elapsed = clock.Elapsed; Assert.True(elapsed < budget);")]
    [InlineData("Stopwatch clock = Stopwatch.StartNew(); clock.Elapsed.Should().BeLessThan(budget);")]
    public void EachSupportedWallClockAssertionShapeIsRejected(string body)
    {
        var findings = WallClockAssertionPolicy.InspectSource(
            "Synthetic.Tests/WallClockTests.cs",
            body.StartsWith("using ", StringComparison.Ordinal)
                ? body
                : $"class C {{ void M() {{ {body} }} }}");

        Assert.Single(findings);
    }

    [Fact]
    public void WallClockDiagnosticOutputOutsideAnAssertionIsAllowed()
    {
        const string source = "class C { void M() { var clock = Stopwatch.StartNew(); Console.WriteLine(clock.Elapsed); Assert.True(completed); } }";

        Assert.Empty(WallClockAssertionPolicy.InspectSource("Synthetic.Tests/GuardTests.cs", source));
    }

    [Theory]
    [InlineData("System.Console.WriteLine(clock.Elapsed);")]
    [InlineData("Console.Error.Write(clock.Elapsed);")]
    [InlineData("Console.Error.WriteLine(clock.Elapsed);")]
    [InlineData("ITestOutputHelper output = null!; output.WriteLine(clock.Elapsed);")]
    [InlineData("ILogger logger = null!; logger.LogInformation(\"elapsed {Elapsed}\", clock.Elapsed);")]
    public void NamedDiagnosticSinksAreAllowed(string diagnostic)
    {
        var source = $"class C {{ void M() {{ var clock = Stopwatch.StartNew(); {diagnostic} }} }}";

        Assert.Empty(WallClockAssertionPolicy.InspectSource("Synthetic.Tests/GuardTests.cs", source));
    }

    [Theory]
    [InlineData("class C { TimeSpan Value; void M() { var clock = Stopwatch.StartNew(); Value = clock.Elapsed; } }")]
    [InlineData("class C { TimeSpan M() { var clock = Stopwatch.StartNew(); return clock.Elapsed; } }")]
    [InlineData("class C { void M(ref TimeSpan value) { var clock = Stopwatch.StartNew(); value = clock.Elapsed; } }")]
    [InlineData("class C { TimeSpan M() => Stopwatch.StartNew().Elapsed; }")]
    [InlineData("class C { void M() { TimeSpan Local() => Stopwatch.StartNew().Elapsed; } }")]
    [InlineData("class C { void M() { var clock = Stopwatch.StartNew(); CheckElapsed(clock.Elapsed); } }")]
    [InlineData("class C { void M() { var clock = Stopwatch.StartNew(); Action<TimeSpan> check = _ => { }; check(clock.Elapsed); } }")]
    [InlineData("class C { void M() { var clock = Stopwatch.StartNew(); clock.Elapsed.CheckElapsed(); } }")]
    public void WallClockFlowsThatEscapeLocalAnalysisFailClosed(string source)
    {
        var finding = Assert.Single(WallClockAssertionPolicy.InspectSource(
            "Synthetic.Tests/UnsupportedFlowTests.cs",
            source));

        Assert.Contains("ASSUMED-UNVERIFIED", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void TaintedReceiverMemberCallFailsClosed()
    {
        const string source = "class C { void M() { var clock = Stopwatch.StartNew(); clock.CheckElapsed(); } }";

        var finding = Assert.Single(WallClockAssertionPolicy.InspectSource(
            "Synthetic.Tests/UnsupportedFlowTests.cs",
            source));

        Assert.Contains("ASSUMED-UNVERIFIED", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void StopwatchStopControlOperationIsAllowed()
    {
        const string source = "class C { void M() { var stopwatch = Stopwatch.StartNew(); stopwatch.Stop(); } }";

        Assert.Empty(WallClockAssertionPolicy.InspectSource("Synthetic.Tests/GuardTests.cs", source));
    }
}
