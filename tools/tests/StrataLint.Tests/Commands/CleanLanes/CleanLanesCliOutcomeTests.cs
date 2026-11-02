using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void CliReturnsExitTwoAndPreservesGlobalFailureStreams()
    {
        const string failedItem =
            "{\"event\":\"clean_lanes_item\",\"kind\":\"idle_pool\","
            + "\"path\":null,\"branch\":null,\"head\":null,\"action\":\"failed\","
            + "\"reason\":\"inventory:pool inventory unavailable\"}\n";
        const string completedItem =
            "{\"event\":\"clean_lanes_item\",\"kind\":\"stale_worktree\","
            + "\"path\":\"/tmp/healthy\",\"branch\":\"harness/healthy\","
            + "\"head\":\"0123456789abcdef\",\"action\":\"removed\","
            + "\"reason\":\"stale_behind\"}\n";
        const string summary =
            "{\"event\":\"clean_lanes_summary\",\"mode\":\"force\","
            + "\"status\":\"failed\",\"extra_sweeps\":\"not_requested\","
            + "\"scope\":\"lanes_only\",\"base_revision\":\"origin/dev\","
            + "\"base_commit\":\"fedcba9876543210\",\"item_count\":2,"
            + "\"removable_count\":1,\"removed_count\":1,\"partial_count\":0,\"failed_count\":1}\n";
        const string error = "CLEAN_LANES_PARTIAL_FAILURE count=1\n";
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(
            new AdmissionOutcome.InfrastructureFailure("unused"),
            cleanLanes: new CommandResult(false, failedItem + completedItem + summary, error));

        var exitCode = CliApplication.Run(
            ["clean-lanes", "--force", "--lanes-only"],
            environment,
            console);

        Assert.Equal(2, exitCode);
        Assert.Equal(failedItem + completedItem + summary, console.Output);
        Assert.Equal(error, console.Error);
        Assert.Equal(["--force", "--lanes-only"], environment.CleanLanesArguments);
    }

    [Fact]
    public void CliReturnsExitZeroAndPreservesSuccessfulCleanLanesStreams()
    {
        const string output = "CLEAN_LANES_OK\n";
        const string error = "CLEAN_LANES_WARNING\n";
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(
            new AdmissionOutcome.InfrastructureFailure("unused"),
            cleanLanes: new CommandResult(true, output, error));

        var exitCode = CliApplication.Run(["clean-lanes"], environment, console);

        Assert.Equal(0, exitCode);
        Assert.Equal(output, console.Output);
        Assert.Equal(error, console.Error);
    }
}
