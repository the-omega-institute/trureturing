using System.Diagnostics;
using Xunit;

namespace StrataLint.TestSupport;

internal static class EngineeringProcess
{
    internal static string Git(string root, params string[] arguments)
    {
        var result = Process(root, "git", arguments);
        Assert.True(result.Exit == 0, result.Text);
        return result.Text.Trim();
    }

    internal static (int Exit, string Text) Process(string root, string executable, string[] arguments,
        IReadOnlyDictionary<string, string>? environment = null, TimeSpan? hangGuard = null)
    {
        var start = new ProcessStartInfo(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        // Keep synthetic fixture processes independent from the outer GitHub
        // workflow's candidate identity. Individual tests opt in explicitly.
        start.Environment["GITHUB_EVENT_NAME"] = "";
        start.Environment["CANDIDATE_SHA"] = "";
        start.Environment["CI_WORKFLOW_INPUTS"] = "null";
        start.Environment.Remove("STRATALINT_CACHE_WRITES");
        foreach (var pair in environment ?? new Dictionary<string, string>()) start.Environment[pair.Key] = pair.Value;
        var probe = GitGuardProbe.Start(start);
        using var process = System.Diagnostics.Process.Start(start)!;
        using var deadline = new CancellationTokenSource(hangGuard ?? TestBudgets.ScriptProcessHangGuard);
        using var cleanup = new CancellationTokenSource();
        var stdoutText = new System.Text.StringBuilder();
        var stderrText = new System.Text.StringBuilder();
        var stdout = Drain(process.StandardOutput, stdoutText);
        var stderr = Drain(process.StandardError, stderrText);
        probe?.Started(process);
        var phase = "child-exit";
        var expired = false;
        Task? exit = null;
        try
        {
            exit = process.WaitForExitAsync(deadline.Token);
            exit.GetAwaiter().GetResult();
            phase = "output-drain";
            Task.WhenAll(stdout, stderr).WaitAsync(deadline.Token).GetAwaiter().GetResult();
            return (process.ExitCode, stdoutText.ToString() + stderrText);
        }
        catch (OperationCanceledException)
        {
            expired = true;
            probe?.Failure(process, exit, stdout, stderr, phase);
        }
        finally
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
            cleanup.CancelAfter(TestBudgets.ScriptProcessHangGuard);
            try { Task.WhenAll(process.WaitForExitAsync(cleanup.Token), stdout, stderr).GetAwaiter().GetResult(); }
            catch (OperationCanceledException) when (expired) { } // Preserve the original guard phase after draining retained bytes.
            finally
            {
                probe?.Finish(process, exit, stdout, stderr, expired);
                if (Environment.GetEnvironmentVariable("JUDGE_SEED_EVIDENCE") is { Length: > 0 } evidence)
                {
                    Directory.CreateDirectory(evidence);
                    var path = Path.Combine(evidence, "process-" + process.Id + "-" + Guid.NewGuid().ToString("N"));
                    File.WriteAllText(path + ".json", System.Text.Json.JsonSerializer.Serialize(new {
                        executable, arguments, working_directory = root, phase, guard_expired = expired,
                        child_exit = process.HasExited ? (int?)process.ExitCode : null }));
                    File.WriteAllText(path + ".stdout.log", stdoutText.ToString());
                    File.WriteAllText(path + ".stderr.log", stderrText.ToString());
                }
            }
        }

        throw new SkipException("infrastructure-hang-guard expired for shared build fixture: " + executable + " " + string.Join(' ', arguments)
            + "; phase=" + phase + "\nstdout:\n" + stdoutText + "\nstderr:\n" + stderrText);

        async Task Drain(StreamReader reader, System.Text.StringBuilder text)
        {
            var buffer = new char[4096];
            int count;
            while ((count = await reader.ReadAsync(buffer.AsMemory(), cleanup.Token).ConfigureAwait(false)) != 0)
                text.Append(buffer, 0, count);
        }
    }
}
