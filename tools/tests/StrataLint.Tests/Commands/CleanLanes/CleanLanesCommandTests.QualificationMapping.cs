using System.Collections;
using System.Reflection;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData("reordered")]
    [InlineData("mixed")]
    [InlineData("failed_protocol")]
    [InlineData("duplicate")]
    [InlineData("missing")]
    [InlineData("deadline")]
    [InlineData("active_deadline")]
    [InlineData("completed_deadline")]
    [InlineData("no_start")]
    [InlineData("cross_path")]
    public void QualificationMappingUsesPathsAndPreservesCompletedResults(string mode)
    {
        var paths = new[] { "/fixture/a space\nnewline", "/fixture/b", "/fixture/c" };
        var rows = paths.Select((path, index) => new { path,
            outcome = index == 0 ? "refused" : index == 1 && mode is "mixed" or "failed_protocol" ? "failed" : "qualified",
            reason = index == 0 ? "locked_recent" : index == 1 && mode is "mixed" or "failed_protocol" ? "qualification_failed:GitFailure:native cause" : null }).Reverse().ToList();
        if (mode == "duplicate") rows.Add(rows[0]);
        if (mode == "missing") rows.RemoveAt(0);
        string Start(string path) => JsonSerializer.Serialize(new { @event = "worktree_qualification_started", path }) + "\n";
        var output = string.Concat(rows.Select(row => (mode == "no_start" ? "" : Start(mode == "cross_path" ? paths[0] : row.path))
            + JsonSerializer.Serialize(new { @event = "worktree_qualification_item", row.path, row.outcome, row.reason }) + "\n"));
        output += JsonSerializer.Serialize(new { @event = "worktree_qualification",
            status = mode is "mixed" or "failed_protocol" ? "failed" : "succeeded", item_count = rows.Count }) + "\n";
        if (mode == "failed_protocol") output += "{invalid row\n";
        var partial = Start(paths[0]) + JsonSerializer.Serialize(new
            { @event = "worktree_qualification_item", path = paths[0], outcome = "refused", reason = "locked_recent" }) + "\n";
        if (mode == "active_deadline") partial += JsonSerializer.Serialize(new
            { @event = "worktree_qualification_started", path = paths[1] }) + "\n";
        var runner = new QualificationStreamRunner(mode is "deadline" or "active_deadline" ? partial : output,
            mode is "mixed" or "failed_protocol" ? 74 : 0, mode is "deadline" or "active_deadline" or "completed_deadline");
        var candidates = paths.Concat([paths[0]]).Select(path => new RegisteredWorktree(path, "head", "branch", "metadata", true, "manual")).ToArray();
        var method = typeof(CleanLanesCommand).GetMethod("QualifyLockedLanes", BindingFlags.Static | BindingFlags.NonPublic)!;
        var results = (IDictionary)method.Invoke(null, ["/fixture", candidates, runner])!;
        Assert.Equal(mode == "completed_deadline" ? 4 : 3, results.Count);
        Assert.Equal(1800, runner.Budget.TotalSeconds);
        Assert.Equal(3, runner.Arguments.Count(argument => argument == "--path"));
        string? Reason(string path) => (string?)results[path]!.GetType().GetProperty("Reason")!.GetValue(results[path]);
        bool Failed(string path) => (bool)results[path]!.GetType().GetProperty("Failed")!.GetValue(results[path])!;
        if (mode == "failed_protocol")
        {
            Assert.Equal("qualification_failed:GitFailure:native cause", Reason(paths[1]));
            Assert.All(paths, path => Assert.True(Failed(path)));
            Assert.Contains("batch_protocol_error", Reason(paths[0]));
            return;
        }
        if (mode is "duplicate" or "missing" or "no_start" or "cross_path")
        {
            foreach (var path in paths)
            {
                Assert.True(Failed(path));
                Assert.Contains("batch_protocol_error", Reason(path));
            }
            return;
        }
        Assert.Equal("locked_recent", Reason(paths[0]));
        Assert.False(Failed(paths[0]));
        if (mode == "completed_deadline")
        {
            Assert.True(Failed(string.Empty));
            Assert.Contains("outer deadline", Reason(string.Empty));
            Assert.Null(Reason(paths[2]));
        }
        else if (mode is "deadline" or "active_deadline")
        {
            foreach (var path in paths.Skip(1))
            {
                Assert.True(Failed(path));
                if (mode == "active_deadline" && path == paths[1])
                {
                    Assert.DoesNotContain("deferred", Reason(path));
                    Assert.Contains("timeout", Reason(path));
                }
                else Assert.Contains("deferred", Reason(path));
                Assert.Contains("outer deadline", Reason(path));
            }
        }
        else
        {
            Assert.Null(Reason(paths[2]));
            Assert.Equal(mode == "mixed", Failed(paths[1]));
            if (mode == "mixed") Assert.Equal("qualification_failed:GitFailure:native cause", Reason(paths[1]));
        }
    }

    private sealed class QualificationStreamRunner(string output, int exit, bool timeout) : IWorktreeProcessRunner
    {
        internal TimeSpan Budget { get; private set; }
        internal IReadOnlyList<string> Arguments { get; private set; } = [];
        public ProcessOutput Run(string file, IReadOnlyList<string> args, string root, TimeSpan budget)
        {
            Budget = budget; Arguments = args;
            if (timeout) throw new TimeoutException("outer deadline");
            return new(exit, Encoding.UTF8.GetBytes(output), []);
        }
        public StreamedProcessOutput<T> RunStreaming<T>(string file, IReadOnlyList<string> args, string root,
            TimeSpan budget, Func<Stream, CancellationToken, Task<T>> read)
        {
            Budget = budget; Arguments = args;
            using var stream = new MemoryStream(Encoding.UTF8.GetBytes(output));
            var value = read(stream, CancellationToken.None).GetAwaiter().GetResult();
            if (timeout) throw new TimeoutException("outer deadline");
            return new(exit, value, []);
        }
    }
}
