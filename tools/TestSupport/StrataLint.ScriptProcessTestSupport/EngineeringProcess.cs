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
        IReadOnlyDictionary<string, string>? environment = null, TimeSpan? hangGuard = null, int? maximumOutputBytes = null)
    {
        var result = Capture(root, executable, arguments, environment, hangGuard, maximumOutputBytes);
        return (result.Exit, result.StandardOutput + result.StandardError);
    }

    internal static (int Exit, string StandardOutput, string StandardError) Capture(
        string root, string executable, string[] arguments,
        IReadOnlyDictionary<string, string>? environment = null, TimeSpan? hangGuard = null, int? maximumOutputBytes = null)
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
        using var process = System.Diagnostics.Process.Start(start)!;
        using var limitedOutput = maximumOutputBytes is { } stdoutLimit
            ? new StreamReader(new LimitedOutputStream(process.StandardOutput.BaseStream, stdoutLimit)) : null;
        using var limitedError = maximumOutputBytes is { } stderrLimit
            ? new StreamReader(new LimitedOutputStream(process.StandardError.BaseStream, stderrLimit)) : null;
        using var deadline = new CancellationTokenSource(hangGuard ?? TestBudgets.ScriptProcessHangGuard);
        using var cleanup = new CancellationTokenSource();
        var stdoutText = new System.Text.StringBuilder();
        var stderrText = new System.Text.StringBuilder();
        var drainFailure = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var stdout = Drain(limitedOutput ?? process.StandardOutput, stdoutText);
        var stderr = Drain(limitedError ?? process.StandardError, stderrText);
        var phase = "child-exit";
        var expired = false;
        try
        {
            CompleteOrFail(process.WaitForExitAsync(deadline.Token));
            phase = "output-drain";
            CompleteOrFail(Task.WhenAll(stdout, stderr).WaitAsync(deadline.Token));
            return (process.ExitCode, stdoutText.ToString(), stderrText.ToString());
        }
        catch (OperationCanceledException)
        {
            expired = true;
        }
        finally
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
            cleanup.CancelAfter(TestBudgets.ScriptProcessHangGuard);
            try { Task.WhenAll(process.WaitForExitAsync(cleanup.Token), stdout, stderr).GetAwaiter().GetResult(); }
            // Preserve the original output failure or guard phase after cleanup.
            catch (Exception) when (expired || drainFailure.Task.IsFaulted) { }
            finally
            {
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

        void CompleteOrFail(Task work) =>
            Task.WhenAny(work, drainFailure.Task).GetAwaiter().GetResult().GetAwaiter().GetResult();

        async Task Drain(StreamReader reader, System.Text.StringBuilder text)
        {
            try
            {
                var buffer = new char[4096];
                int count;
                while ((count = await reader.ReadAsync(buffer.AsMemory(), cleanup.Token).ConfigureAwait(false)) != 0)
                    text.Append(buffer, 0, count);
            }
            catch (Exception error)
            {
                drainFailure.TrySetException(error);
                throw;
            }
        }
    }

    private sealed class LimitedOutputStream(Stream source, int maximumBytes) : Stream
    {
        private long count;
        public override bool CanRead => true;
        public override bool CanSeek => false;
        public override bool CanWrite => false;
        public override long Length => throw new NotSupportedException();
        public override long Position { get => throw new NotSupportedException(); set => throw new NotSupportedException(); }
        public override void Flush() => throw new NotSupportedException();
        public override long Seek(long offset, SeekOrigin origin) => throw new NotSupportedException();
        public override void SetLength(long value) => throw new NotSupportedException();
        public override void Write(byte[] buffer, int offset, int length) => throw new NotSupportedException();
        public override int Read(byte[] buffer, int offset, int length) => Account(source.Read(buffer, offset, length));
        public override async ValueTask<int> ReadAsync(Memory<byte> buffer, CancellationToken cancellationToken = default) =>
            Account(await source.ReadAsync(buffer, cancellationToken).ConfigureAwait(false));
        private int Account(int bytes)
        {
            count += bytes;
            if (count > maximumBytes)
                throw new InvalidOperationException($"process output exceeded {maximumBytes} bytes");
            return bytes;
        }
    }
}
