using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void CliReturnsExitTwoAndPreservesPartialFailureStreams()
    {
        const string partialItem =
            "{\"event\":\"clean_lanes_item\",\"kind\":\"merged_worktree\","
            + "\"path\":\"/tmp/partial\",\"branch\":\"harness/partial\","
            + "\"head\":\"abcdef0123456789\",\"action\":\"partially_removed\","
            + "\"reason\":\"worktree_remove_failed_state_indeterminate\"}\n";
        const string completedItem =
            "{\"event\":\"clean_lanes_item\",\"kind\":\"merged_worktree\","
            + "\"path\":\"/tmp/healthy\",\"branch\":\"harness/healthy\","
            + "\"head\":\"0123456789abcdef\",\"action\":\"removed\","
            + "\"reason\":\"merged_clean\"}\n";
        const string summary =
            "{\"event\":\"clean_lanes_summary\",\"mode\":\"force\","
            + "\"scope\":\"lanes_only\",\"base_revision\":\"origin/dev\","
            + "\"base_commit\":\"fedcba9876543210\",\"item_count\":2,"
            + "\"removable_count\":1,\"removed_count\":1,\"partial_count\":1}\n";
        const string error = "CLEAN_LANES_PARTIAL_FAILURE count=1\n";
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(
            new AdmissionOutcome.InfrastructureFailure("unused"),
            cleanLanes: new CommandResult(false, partialItem + completedItem + summary, error));

        var exitCode = CliApplication.Run(
            ["clean-lanes", "--force", "--lanes-only"],
            environment,
            console);

        Assert.Equal(2, exitCode);
        Assert.Equal(partialItem + completedItem + summary, console.Output);
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

    private static JsonElement ReadSummary(string output)
    {
        foreach (var line in output.Split('\n', StringSplitOptions.RemoveEmptyEntries))
        {
            using var document = JsonDocument.Parse(line);
            if (document.RootElement.GetProperty("event").GetString() == "clean_lanes_summary")
            {
                return document.RootElement.Clone();
            }
        }

        throw new InvalidOperationException("clean-lanes output did not contain a summary");
    }
}
