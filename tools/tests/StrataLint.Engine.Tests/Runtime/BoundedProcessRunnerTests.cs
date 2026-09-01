namespace StrataLint.Engine.Tests;

public sealed class BoundedProcessRunnerTests
{
    [Fact]
    public void ChildExitIsNotMaskedByClosedStandardInputPipe()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = BoundedProcessRunner.Run(
            "/usr/bin/true",
            [],
            Path.GetTempPath(),
            TimeSpan.FromSeconds(10),
            1024,
            new byte[4 * 1024 * 1024]);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Empty(result.StandardError);
    }
}
