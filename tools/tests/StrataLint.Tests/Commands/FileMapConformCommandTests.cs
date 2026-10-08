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

}
