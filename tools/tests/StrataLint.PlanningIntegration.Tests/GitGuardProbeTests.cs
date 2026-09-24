using System.Diagnostics;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.PlanningIntegration.Tests;

public sealed class GitGuardProbeTests
{
    [Fact]
    public void FailureSnapshotRetainsLiveProcessAndPendingDrainWithoutChangingThem()
    {
        using var temporary = new TemporaryDirectory();
        var start = new ProcessStartInfo("git") { WorkingDirectory = temporary.Path };
        start.ArgumentList.Add("add");
        start.ArgumentList.Add(".");
        var probe = GitGuardProbe.Start(start);
        Assert.NotNull(probe);
        // Exercise the actual pre-kill writer, without spawning a hang or waiting for a timer.
        File.WriteAllText(start.Environment["GIT_TRACE2_EVENT"]!, """
            {"event":"start","sid":"probe-test","time":"test-native-time","argv":["SECRET-ARGV"]}
            {"event":"def_param","param":"credential.helper","value":"SECRET-CONFIG"}
            {"event":"def_param","param":"core.fsmonitor","value":"SECRET-COMMAND"}
            {"event":"region_enter","sid":"probe-test","category":"index","label":"do_read_index"}
            {"event":"child_start","sid":"probe-test","child_id":0,"argv":["SECRET-CHILD"]}
            {"event":
            """);
        using var process = Process.GetCurrentProcess();
        var exit = new TaskCompletionSource();
        var drain = new TaskCompletionSource();
        var directory = Path.Combine(TestRepositoryLayout.FindRoot(), "build/ci/logs/engineering/git-guard");
        var before = Directory.GetFiles(directory, "*.failure.json").ToHashSet(StringComparer.Ordinal);
        probe.Failure(process, exit.Task, drain.Task, Task.CompletedTask, "snapshot-self-test");
        var file = Assert.Single(Directory.GetFiles(directory, "*.failure.json"), path => !before.Contains(path));
        var text = File.ReadAllText(file);
        Assert.DoesNotContain("SECRET-", text, StringComparison.Ordinal);
        using var document = JsonDocument.Parse(text);
        var snapshot = document.RootElement.GetProperty("snapshot");
        Assert.Equal("before-kill", snapshot.GetProperty("observation").GetString());
        Assert.Equal(process.Id, snapshot.GetProperty("pid").GetInt32());
        Assert.Equal("False", snapshot.GetProperty("has_exited").GetString());
        Assert.Equal("WaitingForActivation", snapshot.GetProperty("exit_task").GetString());
        Assert.Equal("WaitingForActivation", snapshot.GetProperty("stdout_task").GetString());
        Assert.Equal("RanToCompletion", snapshot.GetProperty("stderr_task").GetString());
        Assert.False(process.HasExited);
        Assert.False(exit.Task.IsCompleted);
        Assert.False(drain.Task.IsCompleted);
        Assert.Equal(1, document.RootElement.GetProperty("trace2").GetProperty("incomplete_lines").GetInt32());
        Assert.StartsWith("UNAVAILABLE:", ProcessCancellationSnapshot.Observe(() => throw new IOException("SECRET-ERROR")), StringComparison.Ordinal);
        // Preserve the synthetic failure evidence with an unmistakable label in the native SID.
        File.Delete(start.Environment["GIT_TRACE2_EVENT"]!);
    }
}
