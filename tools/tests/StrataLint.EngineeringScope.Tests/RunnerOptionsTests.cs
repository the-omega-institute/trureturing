using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class RunnerOptionsTests
{
    [Fact]
    public void CandidateTestInvocationIsPrebuiltWithMinimalVerbosity()
    {
        var arguments = Program.BuildTestArguments("tools/tests/Probe/Probe.csproj", "/tmp/results");
        Assert.Contains("--no-build", arguments);
        Assert.Contains("--no-restore", arguments);
        Assert.Equal("minimal", arguments[Array.IndexOf(arguments.ToArray(), "--verbosity") + 1]);
    }

    [Theory]
    [InlineData("--all")]
    [InlineData("--base")]
    [InlineData("--head")]
    [InlineData("--full")]
    public void RunnerRejectsFullAndHistoricalSelectionOptions(string option)
    {
        using var output = new StringWriter();
        using var error = new StringWriter();
        var exit = Program.Run(["--repository", "/missing-repository", option, "value"],
            output, error);
        Assert.Equal(2, exit);
        Assert.Contains("options must be", error.ToString(), StringComparison.Ordinal);
        Assert.Empty(output.ToString());
    }

}
