using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    private static string GitBlob(string path)
    {
        var result = BoundedProcessRunner.Run(
            "/usr/bin/git",
            ["hash-object", path],
            FindRepositoryRoot(),
            TimeSpan.FromSeconds(10),
            4 * 1024);
        Assert.Equal(0, result.ExitCode);
        return Encoding.UTF8.GetString(result.StandardOutput).TrimEnd();
    }

    [Fact]
    public void WatchLoadsChangedScriptBytesAtTheNextSweepBoundary()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new WatchFreshnessFixture("replace");

        var originalBlob = fixture.ScriptBlob();
        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        var replacementBlob = fixture.ScriptBlob();
        Assert.NotEqual(originalBlob, replacementBlob);
        Assert.Equal([originalBlob, replacementBlob], LoadedScriptBlobs(result.Log));
        Assert.Equal(["replacement-loaded"], fixture.MarkerLines());
        Assert.Contains(
            $"WATCH SCRIPT CHANGED previous_blob={originalBlob} current_blob={replacementBlob}",
            result.Log,
            StringComparison.Ordinal);
    }

    [Fact]
    public void WatchSkipsSweepWhenCurrentScriptCannotBeSnapshotted()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new WatchFreshnessFixture("delete");

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Single(LoadedScriptBlobs(result.Log));
        Assert.Empty(fixture.MarkerLines());
        Assert.Contains("current script unavailable; sweep skipped", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void WatchPreservesNoCheckObservationAcrossFreshSweepProcesses()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new WatchFreshnessFixture("nochecks", dryRun: false);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(2, LoadedScriptBlobs(result.Log).Length);
        Assert.Equal(
            ["pr close 1 --repo fixture/repository", "pr reopen 1 --repo fixture/repository", "pr merge 1 --repo fixture/repository --auto --merge"],
            fixture.GithubCalls());
        Assert.Empty(Directory.GetFiles(fixture.StateDirectory, "nochecks-*"));
    }

    private sealed class WatchFreshnessFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string bin;
        private readonly string calls;
        private readonly bool dryRun;
        private readonly string log;
        private readonly string marker;
        private readonly string mode;
        private readonly string script;

        internal WatchFreshnessFixture(string mode, bool dryRun = true)
        {
            this.mode = mode;
            this.dryRun = dryRun;
            bin = Path.Combine(temporary.Path, "bin");
            calls = Path.Combine(temporary.Path, "github-calls");
            log = Path.Combine(temporary.Path, "shepherd.log");
            marker = Path.Combine(temporary.Path, "replacement-marker");
            script = Path.Combine(temporary.Path, "pr-shepherd.sh");
            StateDirectory = Path.Combine(temporary.Path, "state");
            Directory.CreateDirectory(bin);
            File.Copy(Path.Combine(FindRepositoryRoot(), ShepherdScriptPath), script);
            InstallStubs();
        }

        internal string StateDirectory { get; }

        internal ShepherdResult Run()
        {
            var home = Path.Combine(temporary.Path, "home");
            Directory.CreateDirectory(home);
            var result = BoundedProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                    $"HOME={home}",
                    $"PR_SHEPHERD_ROOT={temporary.Path}",
                    "PR_SHEPHERD_REPO=fixture/repository",
                    $"PR_SHEPHERD_LOG={log}",
                    $"PR_SHEPHERD_PID={Path.Combine(temporary.Path, "shepherd.pid")}",
                    $"PR_SHEPHERD_STATE={StateDirectory}",
                    $"PR_SHEPHERD_CACHE={Path.Combine(temporary.Path, "cache")}",
                    $"PR_TEST_CANONICAL_SCRIPT={script}",
                    $"PR_TEST_CALLS={calls}",
                    $"PR_TEST_MARKER={marker}",
                    $"PR_TEST_MODE={mode}",
                    $"PR_TEST_SWEEP_STATE={Path.Combine(temporary.Path, "sweep-state")}",
                    $"PR_TEST_WATCH_STATE={Path.Combine(temporary.Path, "watch-state")}",
                    $"SHEPHERD_DRYRUN={(dryRun ? "1" : "0")}",
                    "/bin/bash",
                    script,
                    "watch",
                    "0",
                    "1",
                ],
                temporary.Path,
                TimeSpan.FromSeconds(15),
                64 * 1024);
            return new ShepherdResult(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError),
                File.Exists(log) ? File.ReadAllText(log) : string.Empty);
        }

        internal string ScriptBlob() =>
            GitBlob(script);

        internal string[] GithubCalls() =>
            File.Exists(calls) ? File.ReadAllLines(calls) : [];

        internal string[] MarkerLines() =>
            File.Exists(marker) ? File.ReadAllLines(marker) : [];

        public void Dispose() => temporary.Dispose();

        private void InstallStubs()
        {
            WriteExecutable(
                "gh",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "${1:-}" == pr && "${2:-}" == list && " $* " == *" --json autoMergeRequest "* ]]; then
                  count=0
                  [[ ! -f "$PR_TEST_WATCH_STATE" ]] || count="$(cat "$PR_TEST_WATCH_STATE")"
                  count=$((count + 1))
                  printf '%s' "$count" > "$PR_TEST_WATCH_STATE"
                  if [[ "$count" == 1 ]]; then printf '1\n'; else printf '0\n'; fi
                  exit 0
                fi
                if [[ "${1:-}" == pr && "${2:-}" == list ]]; then
                  count=0
                  [[ ! -f "$PR_TEST_SWEEP_STATE" ]] || count="$(cat "$PR_TEST_SWEEP_STATE")"
                  count=$((count + 1))
                  printf '%s' "$count" > "$PR_TEST_SWEEP_STATE"
                  if [[ "$count" == 1 ]]; then
                    case "$PR_TEST_MODE" in
                      replace)
                        replacement="${PR_TEST_CANONICAL_SCRIPT}.replacement"
                        cp "$PR_TEST_CANONICAL_SCRIPT" "$replacement"
                        printf '%s\n' 'printf "%s\n" replacement-loaded >> "$PR_TEST_MARKER"' >> "$replacement"
                        mv "$replacement" "$PR_TEST_CANONICAL_SCRIPT"
                        ;;
                      delete)
                        rm -f "$PR_TEST_CANONICAL_SCRIPT"
                        ;;
                    esac
                  fi
                  if [[ "$PR_TEST_MODE" == nochecks ]]; then
                    printf '1\tMERGEABLE\tBLOCKED\tfeature\thead-oid\tbase-oid\t0\t-\t-\n'
                  fi
                  exit 0
                fi
                if [[ "${1:-}" == pr ]]; then
                  printf '%s\n' "$*" >> "$PR_TEST_CALLS"
                  exit 0
                fi
                exit 97
                """);
            WriteExecutable(
                "sleep",
                """
                #!/usr/bin/env bash
                exit 0
                """);
        }

        private void WriteExecutable(string name, string contents)
        {
            if (OperatingSystem.IsWindows()) return;
            var path = Path.Combine(bin, name);
            File.WriteAllText(path, contents + "\n", new UTF8Encoding(false));
            File.SetUnixFileMode(
                path,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }
    }
}
