using StrataLint.Runtime;
using StrataLint.TestSupport;

namespace StrataLint.Runtime.Tests;

public sealed class BoundedProcessRunnerTests
{
    [Fact]
    public void InterruptionHookDrainsSettlementAndPreservesTheDeadlineFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var stdout = new MemoryStream();
        using var stderr = new MemoryStream();
        var interrupted = false;
        var exception = Assert.Throws<TimeoutException>(() => BoundedProcessRunner.Run("/bin/sh",
            ["-c", "trap 'printf settled; printf retained >&2; exit 0' TERM; " +
                "printf ready; while :; do :; done"], Path.GetTempPath(), TimeSpan.FromSeconds(1), 4096,
            standardOutput: stdout, standardError: stderr, interruptBeforeKill: process =>
            {
                interrupted = true;
                TestProcessRunner.InterruptPythonFixture(process);
            }));
        Assert.True(interrupted);
        Assert.Contains("timed out after 1 seconds", exception.Message, StringComparison.Ordinal);
        Assert.IsAssignableFrom<OperationCanceledException>(exception.InnerException);
        // Settlement produces both EOFs only after the timeout evidence was captured.
        Assert.Contains("snapshot=non-atomic-before-cleanup", exception.Message, StringComparison.Ordinal);
        Assert.Contains("stdout.eof=unknown", exception.Message, StringComparison.Ordinal);
        Assert.Contains("stderr.eof=unknown", exception.Message, StringComparison.Ordinal);
        Assert.Contains("has-exited.before-cleanup=false(cancel-before=true)", exception.Message, StringComparison.Ordinal);
        Assert.Equal("readysettled", System.Text.Encoding.UTF8.GetString(stdout.ToArray()));
        Assert.Equal("retained", System.Text.Encoding.UTF8.GetString(stderr.ToArray()));
    }

    [Fact]
    public void StartupSeamPreservesArgumentsWorkingDirectoryAndExplicitEnvironment()
    {
        var previous = BoundedProcessRunner.StartProcess.Value;
        System.Diagnostics.ProcessStartInfo? observed = null;
        try
        {
            BoundedProcessRunner.StartProcess.Value = process => { observed = process.StartInfo; return false; };
            var exception = Assert.Throws<InvalidOperationException>(() => BoundedProcessRunner.Run(
                "fixture", ["argument with spaces", "$literal"], Path.GetTempPath(),
                TestBudgets.ZeroDuration, 16, new byte[] { 1 }, new Dictionary<string, string> { ["ONLY"] = "value" }));
            Assert.Equal("could not start fixture", exception.Message);
            Assert.NotNull(observed);
            Assert.Equal(["argument with spaces", "$literal"], observed.ArgumentList);
            Assert.Equal(Path.GetTempPath(), observed.WorkingDirectory);
            Assert.Equal("value", Assert.Single(observed.Environment).Value);
            Assert.False(observed.UseShellExecute);
            Assert.True(observed.RedirectStandardInput && observed.RedirectStandardOutput && observed.RedirectStandardError);
        }
        finally { BoundedProcessRunner.StartProcess.Value = previous; }
    }

    [Fact]
    public void CallerCancellationBeforeStartNeverInvokesStartupSeam()
    {
        var previous = BoundedProcessRunner.StartProcess.Value;
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var started = false;
        try
        {
            BoundedProcessRunner.StartProcess.Value = _ => { started = true; return false; };
            Assert.Throws<OperationCanceledException>(() => BoundedProcessRunner.Run(
                "fixture", [], Path.GetTempPath(), TestBudgets.ZeroDuration, 16,
                cancellationToken: cancellation.Token));
            Assert.False(started);
        }
        finally { BoundedProcessRunner.StartProcess.Value = previous; }
    }

    [Fact]
    public void ExpiredBudgetRemainsTimeoutWhileCallerCancellationRemainsCancellation()
    {
        if (OperatingSystem.IsWindows()) return;
        var timeout = Assert.Throws<TimeoutException>(() => BoundedProcessRunner.Run(
            "/bin/sh", ["-c", "while :; do :; done"], Path.GetTempPath(), TestBudgets.ZeroDuration, 16));
        Assert.IsAssignableFrom<OperationCanceledException>(timeout.InnerException);
        Assert.Contains("record-order-only; unknown=not-observed", timeout.Message, StringComparison.Ordinal);
        Assert.Contains("stdin=not-redirected#", timeout.Message, StringComparison.Ordinal);
        Assert.Contains("task-status-sampled-before-cleanup:", timeout.Message, StringComparison.Ordinal);
        Assert.Contains("exception-site=", timeout.Message, StringComparison.Ordinal);
        Assert.Contains("exit-wait.complete=", timeout.Message, StringComparison.Ordinal);
        var classified = Assert.Throws<SkipException>(() => TestProcessRunner.Classify<int>(() => throw timeout, "/bin/sh"));
        Assert.Equal($"infrastructure-hang-guard expired for /bin/sh: {timeout.Message}", classified.Message);
        using var cancellation = new CancellationTokenSource();
        Assert.ThrowsAny<OperationCanceledException>(() => BoundedProcessRunner.RunStreaming<int>(
            "/bin/sh", ["-c", "while :; do :; done"], Path.GetTempPath(), TestBudgets.ScriptProcessHangGuard, 16,
            (_, _) => { cancellation.Cancel(); return Task.FromCanceled<int>(cancellation.Token); },
            cancellationToken: cancellation.Token));
    }

    [Fact]
    public async Task CompletionEvidenceKeepsOrderingUnknownsAndExceptionsWithoutInferringExit()
    {
        using var cancellation = new CancellationTokenSource();
        var observations = new BoundedProcessRunner.CompletionObservations { Cancellation = cancellation.Token };
        observations.Record("stdin.write", "completed(bytes=26)");
        observations.Record("stdout.bytes", "26");
        await observations.ObserveCompletion(Task.CompletedTask, "stdout.complete");
        cancellation.Cancel();
        observations.Record("stdout.bytes", "27");
        var failure = new IOException("original reader failure");
        Assert.Same(failure, await Assert.ThrowsAsync<IOException>(() => observations.ObserveCompletion(
            Task.FromException(failure), "stderr.complete")));
        using var unstarted = new System.Diagnostics.Process();
        var snapshot = observations.Snapshot(unstarted, null, null, null, null, "completion-arbitration",
            new OperationCanceledException("original cancellation", cancellation.Token), default, cancellation.Token);
        Assert.Contains("stdin.write=completed(bytes=26)#1(cancel-requested=false)", snapshot, StringComparison.Ordinal);
        Assert.Contains("stdout.complete=completed#3(cancel-requested=false)", snapshot, StringComparison.Ordinal);
        Assert.Contains("stdout.bytes=27#4(cancel-requested=true)", snapshot, StringComparison.Ordinal);
        Assert.Contains("stdout.bytes.before-cancel=26#2(cancel-requested=false)", snapshot, StringComparison.Ordinal);
        Assert.Contains("stdout.eof=unknown", snapshot, StringComparison.Ordinal);
        Assert.Contains("stderr.complete=threw(System.IO.IOException)", snapshot, StringComparison.Ordinal);
        Assert.Contains("stdin.close=unknown", snapshot, StringComparison.Ordinal);
        Assert.Contains("has-exited.before-cleanup=unknown(threw System.InvalidOperationException:", snapshot, StringComparison.Ordinal);
        Assert.Contains("exception-message=original cancellation; token=shared-linked", snapshot, StringComparison.Ordinal);
        Assert.Contains("exit-wait=not-created", snapshot, StringComparison.Ordinal);
        observations.Record("stdout.eof", "observed");
        Assert.Contains("stdout.eof=unknown", snapshot, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void BothEntryPointsTagFalseStartupResults(bool streaming)
    {
        var previous = BoundedProcessRunner.StartProcess.Value;
        try
        {
            BoundedProcessRunner.StartProcess.Value = _ => false;
            void Run()
            {
                if (streaming)
                    BoundedProcessRunner.RunStreaming("fixture", [], Path.GetTempPath(),
                        TestBudgets.ZeroDuration, 16, (_, _) => Task.FromResult(0));
                else
                    BoundedProcessRunner.Run("fixture", [], Path.GetTempPath(), TestBudgets.ZeroDuration, 16);
            }
            var failure = Assert.Throws<InvalidOperationException>(Run);
            Assert.Equal("could not start fixture", failure.Message);
            Assert.True(BoundedProcessRunner.FailedBeforeStart(failure));
        }
        finally { BoundedProcessRunner.StartProcess.Value = previous; }
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void StartupExceptionsRetainIdentityAndOutOfMemoryExclusion(bool streaming, bool outOfMemory)
    {
        var previous = BoundedProcessRunner.StartProcess.Value;
        Exception original = outOfMemory ? new OutOfMemoryException("startup memory failure")
            : new System.ComponentModel.Win32Exception("startup failure");
        try
        {
            BoundedProcessRunner.StartProcess.Value = _ => throw original;
            void Run()
            {
                if (streaming)
                    BoundedProcessRunner.RunStreaming("fixture", [], Path.GetTempPath(),
                        TestBudgets.ZeroDuration, 16, (_, _) => Task.FromResult(0));
                else
                    BoundedProcessRunner.Run("fixture", [], Path.GetTempPath(), TestBudgets.ZeroDuration, 16);
            }
            var failure = Assert.ThrowsAny<Exception>(Run);
            Assert.Same(original, failure);
            Assert.Equal(!outOfMemory, BoundedProcessRunner.FailedBeforeStart(failure));
            if (outOfMemory) Assert.Empty(failure.Data);
        }
        finally { BoundedProcessRunner.StartProcess.Value = previous; }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ArgumentPreparationFailuresAreOutsideStartupTagging(bool streaming)
    {
        var previous = BoundedProcessRunner.StartProcess.Value;
        var started = false;
        var original = new IOException("argument enumeration failed");
        IEnumerable<string> Arguments()
        {
            yield return "first";
            throw original;
        }
        try
        {
            BoundedProcessRunner.StartProcess.Value = _ => { started = true; return false; };
            void Run()
            {
                if (streaming)
                    BoundedProcessRunner.RunStreaming("fixture", Arguments(), Path.GetTempPath(),
                        TestBudgets.ZeroDuration, 16, (_, _) => Task.FromResult(0));
                else
                    BoundedProcessRunner.Run("fixture", Arguments(), Path.GetTempPath(), TestBudgets.ZeroDuration, 16);
            }
            var failure = Assert.Throws<IOException>(Run);
            Assert.Same(original, failure);
            Assert.False(started);
            Assert.False(BoundedProcessRunner.FailedBeforeStart(failure));
        }
        finally { BoundedProcessRunner.StartProcess.Value = previous; }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ReaderFailuresAfterStartupRetainIdentityWithoutStartupTagging(bool synchronous)
    {
        if (OperatingSystem.IsWindows()) return;
        var original = new FormatException("reader failure after startup");
        var failure = Assert.Throws<FormatException>(() => BoundedProcessRunner.RunStreaming<int>(
            "/bin/sh", ["-c", "while :; do :; done"], Path.GetTempPath(),
            BoundedProcessRunner.HangDetectionBudget, 16,
            (_, _) => synchronous ? throw original : Task.FromException<int>(original)));
        Assert.Same(original, failure);
        Assert.False(BoundedProcessRunner.FailedBeforeStart(failure));
    }

    [Fact]
    public void CallerCancellationWithoutInterruptionHookDrainsThroughEof()
    {
        if (OperatingSystem.IsWindows()) return;
        using var cancellation = new CancellationTokenSource();
        CancellationToken ioToken = default;
        var eof = false;
        var bytes = new byte[5];
        var failure = Assert.ThrowsAny<OperationCanceledException>(() => BoundedProcessRunner.RunStreaming<int>(
            "/bin/sh", ["-c", "printf ready; while :; do :; done"], Path.GetTempPath(),
            BoundedProcessRunner.HangDetectionBudget, 16,
            async (stream, token) =>
            {
                ioToken = token;
                await stream.ReadExactlyAsync(bytes, token);
                cancellation.Cancel();
                eof = await stream.ReadAsync(new byte[1], token) == 0;
                return 0;
            }, cancellationToken: cancellation.Token));
        Assert.Equal("ready", System.Text.Encoding.UTF8.GetString(bytes));
        Assert.True(eof);
        Assert.True(ioToken.CanBeCanceled);
        Assert.False(ioToken.IsCancellationRequested);
        Assert.False(BoundedProcessRunner.FailedBeforeStart(failure));
    }

    [Fact]
    public void DrainWithoutInterruptionHookStillCancelsAnUnfinishedReader()
    {
        if (OperatingSystem.IsWindows()) return;
        using var cancellation = new CancellationTokenSource();
        CancellationToken ioToken = default;
        var failure = Assert.ThrowsAny<OperationCanceledException>(() => BoundedProcessRunner.RunStreaming<int>(
            "/bin/sh", ["-c", "while :; do :; done"], Path.GetTempPath(),
            BoundedProcessRunner.HangDetectionBudget, 16,
            async (_, token) =>
            {
                ioToken = token;
                cancellation.Cancel();
                await Task.Delay(Timeout.Infinite, token);
                return 0;
            }, cancellationToken: cancellation.Token));
        Assert.True(ioToken.IsCancellationRequested);
        Assert.NotEqual(cancellation.Token, ioToken);
        Assert.False(BoundedProcessRunner.FailedBeforeStart(failure));
    }

    [Xunit.SkippableTheory]
    [InlineData(false, 16)]
    [InlineData(false, 17)]
    [InlineData(true, 16)]
    [InlineData(true, 17)]
    public void ForwardedStreamsRetainExactBytesAndExistingOutputBounds(bool stderr, int bytes)
    {
        if (OperatingSystem.IsWindows()) return;
        using var forwarded = new MemoryStream();
        void RunAndAssert()
        {
            var result = TestProcessRunner.Run(
                "/bin/sh", ["-c", "head -c \"$1\" /dev/zero" + (stderr ? " >&2" : ""),
                    "forwarded-probe", bytes.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                Path.GetTempPath(), BoundedProcessRunner.HangDetectionBudget, 16,
                standardOutput: stderr ? null : forwarded, standardError: stderr ? forwarded : null);
            Assert.Equal(0, result.ExitCode);
            Assert.Equal(new byte[bytes], forwarded.ToArray());
            Assert.Equal(forwarded.ToArray(), stderr ? result.StandardError : result.StandardOutput);
            Assert.Empty(stderr ? result.StandardOutput : result.StandardError);
        }
        if (bytes <= 16) RunAndAssert();
        else Assert.Contains("process output exceeded 16 bytes",
            Assert.Throws<InvalidOperationException>(RunAndAssert).Message, StringComparison.Ordinal);
        Assert.True(forwarded.Length <= 16);
    }

    [Xunit.SkippableTheory]
    [InlineData(false, 16)]
    [InlineData(false, 17)]
    [InlineData(true, 16)]
    [InlineData(true, 17)]
    public void BufferedStdoutAndStreamingStderrKeepTheirBounds(bool stderr, int bytes)
    {
        if (OperatingSystem.IsWindows()) return;
        void RunAndAssert()
        {
            var count = bytes.ToString(System.Globalization.CultureInfo.InvariantCulture);
            if (stderr)
            {
                var result = TestProcessRunner.Classify(() => BoundedProcessRunner.RunStreaming(
                    "/bin/sh", ["-c", "head -c \"$1\" /dev/zero >&2", "stderr-probe", count],
                    Path.GetTempPath(), BoundedProcessRunner.HangDetectionBudget, 16,
                    async (stream, cancellation) =>
                    {
                        using var reader = new StreamReader(stream);
                        return await reader.ReadToEndAsync(cancellation);
                    }), "/bin/sh");
                Assert.Equal(0, result.ExitCode);
                Assert.Empty(result.StandardOutput);
                Assert.Equal(bytes, result.StandardError.Length);
            }
            else
            {
                var result = TestProcessRunner.Run(
                    "/usr/bin/head", ["-c", count, "/dev/zero"], Path.GetTempPath(),
                    BoundedProcessRunner.HangDetectionBudget, 16);
                Assert.Equal(0, result.ExitCode);
                Assert.Equal(bytes, result.StandardOutput.Length);
            }
        }
        InvalidOperationException? exceeded = null;
        try { RunAndAssert(); }
        catch (InvalidOperationException exception) { exceeded = exception; }
        if (bytes <= 16) Assert.Null(exceeded);
        else Assert.Contains("process output exceeded 16 bytes",
            Assert.IsType<InvalidOperationException>(exceeded).Message, StringComparison.Ordinal);
    }

    [Xunit.SkippableFact]
    public void StreamingOutputDoesNotApplyStderrLimitToStdout()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = TestProcessRunner.Classify(() => BoundedProcessRunner.RunStreaming(
            "/usr/bin/head", ["-c", "4096", "/dev/zero"], Path.GetTempPath(),
            BoundedProcessRunner.HangDetectionBudget, 16,
            async (stream, cancellation) =>
            {
                var buffer = new byte[257];
                var total = 0;
                int count;
                while ((count = await stream.ReadAsync(buffer, cancellation)) != 0) total += count;
                return total;
            }), "/usr/bin/head");

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(4096, result.StandardOutput);
        Assert.Empty(result.StandardError);
    }

    [Xunit.SkippableFact]
    public void StreamingOutputPreservesChildExitAndStderr()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = TestProcessRunner.Classify(() => BoundedProcessRunner.RunStreaming(
            "/bin/sh", ["-c", "printf out; printf err >&2; exit 7"], Path.GetTempPath(),
            BoundedProcessRunner.HangDetectionBudget, 16,
            async (stream, cancellation) =>
            {
                using var reader = new StreamReader(stream);
                return await reader.ReadToEndAsync(cancellation);
            }), "/bin/sh");

        Assert.Equal(7, result.ExitCode);
        Assert.Equal("out", result.StandardOutput);
        Assert.Equal("err", System.Text.Encoding.UTF8.GetString(result.StandardError));
    }

    [Xunit.SkippableTheory]
    [InlineData(false)]
    [InlineData(true)]
    public void OutputLimitFailureIsNotMaskedByBlockedProducer(bool stderr)
    {
        if (OperatingSystem.IsWindows()) return;

        // Exceed pipe capacity as well as the reader limit: a child that can
        // finish writing before the reader fails does not exercise this fault.
        var redirect = stderr ? " >&2" : string.Empty;
        InvalidOperationException? exceeded = null;
        try
        {
            TestProcessRunner.Run("/bin/sh",
                ["-c", "head -c 1048576 /dev/zero" + redirect], Path.GetTempPath(),
                BoundedProcessRunner.HangDetectionBudget, 16);
        }
        catch (InvalidOperationException exception) { exceeded = exception; }

        Assert.Equal("process output exceeded 16 bytes",
            Assert.IsType<InvalidOperationException>(exceeded).Message);
    }

    [Xunit.SkippableFact]
    public void StreamingParserFailureIsNotMaskedByBlockedProducer()
    {
        if (OperatingSystem.IsWindows()) return;

        FormatException? invalid = null;
        try
        {
            TestProcessRunner.Classify(() => BoundedProcessRunner.RunStreaming<int>("/usr/bin/head",
                ["-c", "1048576", "/dev/zero"], Path.GetTempPath(),
                BoundedProcessRunner.HangDetectionBudget, 16,
                async (stream, cancellation) =>
                {
                    await stream.ReadExactlyAsync(new byte[1], cancellation);
                    throw new FormatException("invalid history record");
                }), "/usr/bin/head");
        }
        catch (FormatException exception) { invalid = exception; }

        Assert.Equal("invalid history record", Assert.IsType<FormatException>(invalid).Message);
    }

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
