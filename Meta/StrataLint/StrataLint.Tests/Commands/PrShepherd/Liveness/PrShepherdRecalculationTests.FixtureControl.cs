using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    private sealed partial class ShepherdFixture
    {
        internal string WatchState() => File.ReadAllText(WatchStatePath);

        internal void WaitForWatchPhase(string phase)
        {
            var expected = $"phase={phase}\n";
            for (var attempt = 0; attempt < 200; attempt++)
            {
                if (File.Exists(WatchStatePath)
                    && File.ReadAllText(WatchStatePath).Contains(expected, StringComparison.Ordinal))
                {
                    return;
                }
                Thread.Sleep(20);
            }
            Assert.Fail($"watch did not reach phase={phase}\n{(File.Exists(WatchStatePath) ? WatchState() : "state missing")}");
        }

        internal void ReplaceWatchStateField(string name, string value)
        {
            var lines = File.ReadAllLines(WatchStatePath);
            var prefix = name + "=";
            var index = Array.FindIndex(lines, line => line.StartsWith(prefix, StringComparison.Ordinal));
            Assert.True(index >= 0, $"missing watch state field {name}");
            lines[index] = prefix + value;
            File.WriteAllLines(WatchStatePath, lines, new UTF8Encoding(false));
        }

        internal int ReadOwnerPid()
        {
            var line = File.ReadAllLines(WatchOwnerPath)
                .Single(value => value.StartsWith("pid=", StringComparison.Ordinal));
            return int.Parse(line[4..], System.Globalization.CultureInfo.InvariantCulture);
        }

        internal void CorruptWatchOwner() =>
            File.WriteAllText(WatchOwnerPath, "unverifiable-owner\n", new UTF8Encoding(false));

        internal void ReplaceWatchOwner(int pid)
        {
            var processStart = BoundedProcessRunner.Run(
                Path.Combine(bin, "ps"),
                ["-p", pid.ToString(), "-o", "lstart="],
                repository,
                TimeSpan.FromSeconds(2),
                4 * 1024);
            Assert.Equal(0, processStart.ExitCode);
            File.WriteAllText(
                WatchOwnerPath,
                "schema=pr-watch-owner-v1\n"
                + $"pid={pid}\n"
                + $"process_start={Encoding.UTF8.GetString(processStart.StandardOutput).Trim()}\n"
                + $"canonical_script={Path.Combine(repository, ShepherdScriptPath)}\n",
                new UTF8Encoding(false));
        }

        internal void RemoveWatchOwner() => File.Delete(WatchOwnerPath);

        internal void WaitForHangingProcesses()
        {
            for (var attempt = 0; attempt < 500; attempt++)
            {
                if (HangingProcessIds().Length >= 2) return;
                Thread.Sleep(20);
            }
            Assert.Fail($"bounded command did not start\n{(File.Exists(log) ? File.ReadAllText(log) : "log missing")}");
        }

        internal TimeSpan TerminateWatch(TimeSpan maximumWait)
        {
            var stopwatch = System.Diagnostics.Stopwatch.StartNew();
            var pid = startedWatchPid;
            Assert.True(pid > 0, "watch owner pid is unavailable");
            _ = BoundedProcessRunner.Run(
                "/bin/kill",
                ["-TERM", pid.ToString()],
                repository,
                TimeSpan.FromSeconds(2),
                4 * 1024);
            while (stopwatch.Elapsed < maximumWait && IsProcessAlive(pid)) Thread.Sleep(20);
            stopwatch.Stop();
            if (IsProcessAlive(pid))
            {
                _ = BoundedProcessRunner.Run(
                    "/bin/kill",
                    ["-KILL", pid.ToString()],
                    repository,
                    TimeSpan.FromSeconds(2),
                    4 * 1024);
            }
            startedWatchPid = 0;
            return stopwatch.Elapsed;
        }

        internal void StopWatch(int? ownerPid = null)
        {
            var pid = ownerPid ?? startedWatchPid;
            if (pid <= 0) return;
            _ = BoundedProcessRunner.Run(
                "/bin/kill",
                ["-TERM", pid.ToString()],
                repository,
                TimeSpan.FromSeconds(2),
                4 * 1024);
            for (var attempt = 0; attempt < 100 && IsProcessAlive(pid); attempt++)
            {
                Thread.Sleep(20);
            }
            startedWatchPid = 0;
        }

        internal string RemoteHead() =>
            GitOutput(temporary.Path, "--git-dir", origin, "rev-parse", $"refs/heads/{headBranch}");

        internal bool IsAncestor(string ancestor, string descendant) =>
            GitResult(repository, "merge-base", "--is-ancestor", ancestor, descendant).ExitCode == 0;

        internal string ShowRemote(string path) =>
            GitResult(
                temporary.Path,
                "--git-dir",
                origin,
                "show",
                $"refs/heads/{headBranch}:{path}").Output;

        internal bool RemoteContains(string path) =>
            GitResult(
                temporary.Path,
                "--git-dir",
                origin,
                "cat-file",
                "-e",
                $"refs/heads/{headBranch}:{path}").ExitCode == 0;

        internal int CountCommitsWithSubject(string subject, string? revision = null) =>
            GitOutput(
                    temporary.Path,
                    "--git-dir",
                    origin,
                    "log",
                    "--format=%s",
                    revision ?? $"refs/heads/{headBranch}")
                .Split('\n', StringSplitOptions.RemoveEmptyEntries)
                .Count(line => string.Equals(line, subject, StringComparison.Ordinal));

        public void Dispose()
        {
            StopWatch();
            temporary.Dispose();
        }

        private static void Write(string root, string relativePath, string contents)
        {
            var path = Path.Combine(root, relativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, contents, new UTF8Encoding(false));
        }

        private static void Git(string workingDirectory, params string[] arguments)
        {
            var result = GitResult(workingDirectory, arguments);
            Assert.True(
                result.ExitCode == 0,
                $"git {string.Join(' ', arguments)} failed ({result.ExitCode}): {result.Error}");
        }

        private static string GitOutput(string workingDirectory, params string[] arguments)
        {
            var result = GitResult(workingDirectory, arguments);
            Assert.True(
                result.ExitCode == 0,
                $"git {string.Join(' ', arguments)} failed ({result.ExitCode}): {result.Error}");
            return result.Output.TrimEnd();
        }

        private static CommandResult GitResult(string workingDirectory, params string[] arguments)
        {
            var result = BoundedProcessRunner.Run(
                "/usr/bin/git",
                arguments,
                workingDirectory,
                TimeSpan.FromSeconds(15),
                64 * 1024);
            return new CommandResult(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError));
        }
    }
}
