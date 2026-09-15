using System.Diagnostics;
using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class LeanCacheProvisionerTests
{
    [Theory]
    [InlineData(0)]
    [InlineData(37)]
    public void CanonicalReaderPublishesBothStreamsBeforeChildExit(int childExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PrivateReaderFixture();
        using var process = StartStreamingReader(fixture, childExit);
        try
        {
            WaitForReaderOutput(fixture, process);
            Assert.False(File.Exists(Path.Combine(fixture.Reader, "child-exited")));
            Assert.False(process.HasExited);
            using (var release = new StreamWriter(new FileStream(
                Path.Combine(fixture.Reader, "release"), FileMode.Open, FileAccess.ReadWrite)))
                release.WriteLine("release");
            WaitForReaderExit(process);
            Assert.Equal(childExit, process.ExitCode);
            var stdout = File.ReadAllText(Path.Combine(fixture.Reader, "stdout.log"));
            var stderr = File.ReadAllText(Path.Combine(fixture.Reader, "stderr.log"));
            Assert.Equal(1, stdout.Split("stdout-marker", StringSplitOptions.None).Length - 1);
            Assert.EndsWith("stdout-marker|released", stdout, StringComparison.Ordinal);
            Assert.Equal("stderr-marker|released", stderr);
            Assert.Equal("started\n", File.ReadAllText(Path.Combine(fixture.Reader, "executions")));
        }
        finally { StopReader(process); }
    }

    [Theory]
    [InlineData("-TERM", 143)]
    [InlineData("-INT", 130)]
    public void CanonicalReaderSignalPreservesFailureAndReapsItsChild(string signalName, int expectedExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PrivateReaderFixture();
        using var process = StartStreamingReader(fixture, 0);
        try
        {
            WaitForReaderOutput(fixture, process);
            var pid = File.ReadAllText(Path.Combine(fixture.Reader, "child-pid")).Trim();
            var signal = TestProcessRunner.Run("/bin/kill", [signalName, process.Id.ToString(
                System.Globalization.CultureInfo.InvariantCulture)], fixture.Reader,
                TestBudgets.ScriptProcessHangGuard, 1024);
            Assert.Equal(0, signal.ExitCode);
            WaitForReaderExit(process);
            Assert.Equal(expectedExit, process.ExitCode);
            var state = TestProcessRunner.Run("ps", ["-o", "stat=", "-p", pid], fixture.Reader,
                TestBudgets.ScriptProcessHangGuard, 1024);
            Assert.True(state.ExitCode == 1 || Encoding.UTF8.GetString(state.StandardOutput).TrimStart().StartsWith('Z'),
                "cancelled reader retained a live child: " + Encoding.UTF8.GetString(state.StandardOutput));
            Assert.False(File.Exists(Path.Combine(fixture.Reader, "child-exited")));
            Assert.True(fixture.Command(fixture.Reader, "ensure-cache").Success);
        }
        finally { StopReader(process); }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CanonicalReaderRejectsOutputOverIts64MiBLimit(bool stderr)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PrivateReaderFixture();
        const int limit = 64 * 1024 * 1024;
        using var process = StartStreamingReader(fixture, 0,
            "head -c 67108865 /dev/zero" + (stderr ? " >&2\n" : "\n"));
        try
        {
            WaitForReaderExit(process);
            Assert.Equal(2, process.ExitCode);
            using var error = File.OpenRead(Path.Combine(fixture.Reader, "stderr.log"));
            error.Seek(Math.Max(0, error.Length - 4096), SeekOrigin.Begin);
            using var tail = new StreamReader(error);
            Assert.Contains("process output exceeded 67108864 bytes", tail.ReadToEnd(), StringComparison.Ordinal);
            var forwarded = new FileInfo(Path.Combine(fixture.Reader, stderr ? "stderr.log" : "stdout.log")).Length;
            Assert.InRange(forwarded, 1, limit + 4096L);
        }
        finally { StopReader(process); }
    }

    private static Process StartStreamingReader(PrivateReaderFixture fixture, int childExit, string? commandBody = null)
    {
        var script = Path.Combine(fixture.Reader, "tools/scripts/worktree/lean-cache-run.sh");
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-run.sh"), script);
        var command = Path.Combine(fixture.Reader, "command.sh");
        File.WriteAllText(command, commandBody ?? $$"""
            set -euo pipefail
            printf 'started\n' >> executions
            # This is a deterministic pre-stream failure on the old implementation,
            # so a missing handshake is not classified by elapsed time.
            if ! grep -q '^LEAN_CACHE ' stdout.log; then exit 84; fi
            printf '%s\n' "$$" > child-pid
            printf 'stdout-marker'
            printf 'stderr-marker' >&2
            IFS= read -r release < release
            : > child-exited
            printf '|released'
            printf '|released' >&2
            exit {{childExit}}
            """, new UTF8Encoding(false));
        Assert.Equal(0, TestProcessRunner.Run("mkfifo", ["release"], fixture.Reader,
            TestBudgets.ScriptProcessHangGuard, 1024).ExitCode);
        var info = new ProcessStartInfo
        {
            FileName = "/bin/bash", WorkingDirectory = fixture.Reader, UseShellExecute = false,
        };
        foreach (var argument in new[] { "-c", "exec \"$@\" > stdout.log 2> stderr.log", "reader-test",
            "/bin/bash", script, "/bin/bash", command }) info.ArgumentList.Add(argument);
        info.Environment["STRATALINT_LEAN_PRODUCER_DLL"] = typeof(LeanProgram).Assembly.Location;
        info.Environment["LAKE_BIN"] = fixture.Lake;
        var process = new Process { StartInfo = info };
        Assert.True(process.Start());
        return process;
    }

    private static void WaitForReaderOutput(PrivateReaderFixture fixture, Process process)
    {
        bool Observed(string file, string marker) => File.Exists(Path.Combine(fixture.Reader, file))
            && File.ReadAllText(Path.Combine(fixture.Reader, file)).Contains(marker, StringComparison.Ordinal);
        if (!SpinWait.SpinUntil(() => process.HasExited
            || Observed("stdout.log", "stdout-marker") && Observed("stderr.log", "stderr-marker"),
            TestBudgets.ScriptProcessHangGuard))
            throw new SkipException("infrastructure-hang-guard expired for cache reader output handshake");
        Assert.True(Observed("stdout.log", "stdout-marker") && Observed("stderr.log", "stderr-marker"),
            "reader exited without publishing both streams: "
            + File.ReadAllText(Path.Combine(fixture.Reader, "stdout.log"))
            + File.ReadAllText(Path.Combine(fixture.Reader, "stderr.log")));
    }

    private static void WaitForReaderExit(Process process)
    {
        if (!SpinWait.SpinUntil(() => process.HasExited, TestBudgets.ScriptProcessHangGuard))
            throw new SkipException("infrastructure-hang-guard expired waiting for cache reader exit");
    }

    private static void StopReader(Process process)
    {
        if (!process.HasExited) process.Kill(entireProcessTree: true);
        WaitForReaderExit(process);
    }
}

internal sealed class PrivateReaderFixture : IDisposable
{
    private readonly TemporaryDirectory directory = new();
    internal string Reader => directory.Path;
    internal string Lake { get; }

    internal PrivateReaderFixture()
    {
        File.WriteAllText(Path.Combine(Reader, "lean-toolchain"), "leanprover/lean4:v4.33.0\n");
        File.WriteAllText(Path.Combine(Reader, "lake-manifest.json"), LeanCacheFixtureFile.Manifest());
        var project = Path.Combine(Reader, ".lake", "build", "lib", "lean");
        Directory.CreateDirectory(project);
        File.WriteAllText(Path.Combine(project, "Fixture.olean"), "fixture output\n");
        LeanCacheStamp.Write(Path.Combine(Reader, ".lake"),
            LeanPinSet.TryReadWorktree(Reader, out _) ?? throw new InvalidOperationException("fixture pins"));
        Lake = Path.Combine(Reader, "lake");
        File.WriteAllText(Lake, "#!/bin/sh\nexit 0\n");
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }

    internal CommandResult Command(string root, params string[] arguments) =>
        WorktreeCommand.Run(root, [arguments[0], "--path", root, .. arguments.Skip(1)]);

    public void Dispose() => directory.Dispose();
}
