using System.Collections;
using System.Diagnostics;
using System.Reflection;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData("before_start")]
    [InlineData("after_start")]
    [InlineData("after_item")]
    [InlineData("partial_start")]
    [InlineData("partial_item")]
    [InlineData("completed")]
    public void QualificationProductionDeadlineDrainsCompleteEvents(string boundary)
    {
        var paths = new[] { "/fixture/a", "/fixture/b", "/fixture/c" };
        string Start(string path) => JsonSerializer.Serialize(new { @event = "worktree_qualification_started", path }) + "\n";
        string Item(string path) => JsonSerializer.Serialize(new
            { @event = "worktree_qualification_item", path, outcome = "qualified", reason = (string?)null }) + "\n";
        var emitted = boundary switch
        {
            "before_start" => "",
            "after_start" => Start(paths[0]),
            "partial_start" => Start(paths[0]) + Item(paths[0]) + Start(paths[1])[..^4],
            "partial_item" => Start(paths[0]) + Item(paths[0]) + Start(paths[1]) + Item(paths[1])[..^4],
            "completed" => string.Concat(paths.Select(path => Start(path) + Item(path)))
                + JsonSerializer.Serialize(new { @event = "worktree_qualification", status = "succeeded", item_count = 3 }) + "\n",
            _ => Start(paths[0]) + Item(paths[0]) + Start(paths[1]),
        };
        var runner = new BufferedQualificationProcessRunner(emitted);
        var candidates = paths.Select(path => new RegisteredWorktree(path, "head", "branch", "metadata", true, "manual")).ToArray();
        var method = typeof(CleanLanesCommand).GetMethod("QualifyLockedLanes", BindingFlags.Static | BindingFlags.NonPublic)!;
        var results = (IDictionary)method.Invoke(null, [Path.GetTempPath(), candidates, runner])!;
        string Outcome(string path) => results[path]!.GetType().GetProperty("Outcome")!.GetValue(results[path])!.ToString()!;
        string? Reason(string path) => (string?)results[path]!.GetType().GetProperty("Reason")!.GetValue(results[path]);
        Assert.Equal(1800, runner.RequestedBudget.TotalSeconds);
        Assert.True(runner.ChildSettled);
        Assert.Equal(boundary == "before_start" ? "Deferred" : boundary == "after_start" ? "Failed" : "Eligible", Outcome(paths[0]));
        Assert.Equal(boundary == "completed" ? "Eligible" : boundary is "after_item" or "partial_item" ? "Failed" : "Deferred", Outcome(paths[1]));
        Assert.Equal(boundary == "completed" ? "Eligible" : "Deferred", Outcome(paths[2]));
        Assert.Contains("timed out", Reason(boundary == "completed" ? "" : paths[2]));
    }

    private sealed class BufferedQualificationProcessRunner(string emitted) : IWorktreeProcessRunner
    {
        internal TimeSpan RequestedBudget { get; private set; }
        internal bool ChildSettled { get; private set; }
        public ProcessOutput Run(string file, IReadOnlyList<string> args, string root, TimeSpan budget) =>
            throw new NotSupportedException();
        public StreamedProcessOutput<T> RunStreaming<T>(string file, IReadOnlyList<string> args, string root,
            TimeSpan budget, Func<Stream, CancellationToken, Task<T>> read)
        {
            RequestedBudget = budget;
            Process? child = null;
            var previous = BoundedProcessRunner.StartProcess.Value;
            try
            {
                BoundedProcessRunner.StartProcess.Value = process => { child = process; return process.Start(); };
                return new ProductionWorktreeProcessRunner().RunStreaming("python3",
                    ["-IB", "-c", "import sys,time; sys.stdout.write(" + JsonSerializer.Serialize(emitted)
                        + "); sys.stdout.flush(); time.sleep(30)"], root, TimeSpan.FromSeconds(1), async (stream, cancellation) =>
                    {
                        // Hold consumption until the real child has been killed by its deadline.
                        await child!.WaitForExitAsync();
                        ChildSettled = true;
                        return await read(stream, cancellation);
                    });
            }
            finally { BoundedProcessRunner.StartProcess.Value = previous; }
        }
    }
}
