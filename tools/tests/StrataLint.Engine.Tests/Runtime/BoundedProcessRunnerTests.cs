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
            var result = TestProcessRunner.Classify(() => BoundedProcessRunner.Run(
                "/bin/sh", ["-c", "head -c \"$1\" /dev/zero" + (stderr ? " >&2" : ""),
                    "forwarded-probe", bytes.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                Path.GetTempPath(), BoundedProcessRunner.HangDetectionBudget, 16,
                standardOutput: stderr ? null : forwarded, standardError: stderr ? forwarded : null), "/bin/sh");
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
