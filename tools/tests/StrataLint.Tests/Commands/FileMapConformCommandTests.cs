using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FileMapConformCommandTests
{
    [Fact]
    public void TopLevelDispatchRoutesFileMapConform()
    {
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(
            new AdmissionOutcome.InfrastructureFailure("unused"),
            fileMapConform: new ExplicitCommandResult(1, "synthetic finding\n", string.Empty));

        var exit = CliApplication.Run(["filemap-conform"], environment, console);

        Assert.Equal(1, exit);
        Assert.Equal("synthetic finding\n", console.Output);
        Assert.Equal(string.Empty, console.Error);
    }

    [Fact]
    public void EmptySyntheticFindingsReturnZeroWithoutOutput()
    {
        var result = FileMapConformCommand.Render([]);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(string.Empty, result.Output);
        Assert.Equal(string.Empty, result.Error);
    }

    [Fact]
    public void SyntheticFindingsArePrintedOnePerLineAndReturnOne()
    {
        var result = FileMapConformCommand.Render(
        [
            new FileMapFinding("FILEMAP-Z", "z", "last"),
            new FileMapFinding("FILEMAP-A", "a", "first"),
        ]);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal("FILEMAP-A a: first\nFILEMAP-Z z: last\n", result.Output);
        Assert.Equal(string.Empty, result.Error);
    }

    [Fact]
    public void ArgumentsAreRejectedAsInfrastructureUsage()
    {
        var result = FileMapConformCommand.Run(["unexpected"], "fixture-root");

        Assert.Equal(2, result.ExitCode);
        Assert.Equal(string.Empty, result.Output);
        Assert.Contains("USAGE: StrataLint filemap-conform", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingStrictManifestIsAnInfrastructureFailure()
    {
        using var directory = new TemporaryDirectory();

        var result = FileMapConformCommand.Run([], directory.Path);

        Assert.Equal(2, result.ExitCode);
        Assert.Equal(string.Empty, result.Output);
        Assert.Contains("INFRASTRUCTURE_FAILURE filemap-conform", result.Error, StringComparison.Ordinal);
    }
}
