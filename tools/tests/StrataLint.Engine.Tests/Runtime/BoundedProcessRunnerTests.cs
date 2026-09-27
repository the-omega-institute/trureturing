using StrataLint.TestSupport;

namespace StrataLint.Engine.Tests;

public sealed class BoundedProcessRunnerTests
{
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
