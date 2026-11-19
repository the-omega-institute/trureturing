using System.Diagnostics;
using System.Globalization;
using System.Text;
using System.Runtime.ExceptionServices;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.ReportSupervisor.Tests;

// Source-only candidate against dev 2d9656471f9435e6e26e89ca61fbe70b1cdcef8d.
// Native compilation/execution and current-branch pin reconciliation remain required.
// Uses the existing fixture and its infrastructure hang guard. No timing assertion.
public sealed class ReportSupervisorPollDelayTests
{
    [Theory]
    [InlineData(false, 0)]
    [InlineData(false, 7)]
    [InlineData(true, 0)]
    [InlineData(true, 7)]
    public void FailedPollDelayPreservesHealthyWorkerAndItsExit(bool persistent, int workerExit)
    {
        WithRun(persistent, workerExit, run =>
        {
            run.Start();
            run.ArmFaultAfterRealWorkerReady();
            run.ReleaseWorker();
            var stderr = run.Finish(workerExit);

            Assert.Equal(workerExit.ToString(CultureInfo.InvariantCulture),
                File.ReadAllText(run.Done).Trim());
            Assert.Equal("1", File.ReadAllText(run.SleepCount).Trim());
            Assert.Contains("polling delay unavailable (exit=137)", stderr, StringComparison.Ordinal);
            run.AssertClean();
        });
    }

    [Fact]
    public void PersistentFailureUsesRealBuiltinTimersAndDoesNotRetrySleep()
    {
        using var fixture = new ReportSupervisorFixture();
        var function = PollFunction(fixture);
        var harness = """
            set -euo pipefail
            TMP_ROOT="$PWD"
            POLL_DELAY_FIFO=''
            POLL_DELAY_FALLBACK=0
            sleeps=0
            timers=0
            sleep() { sleeps=$((sleeps + 1)); return 137; }
            read() {
              timers=$((timers + 1))
              builtin read "$@"
            }
            """ + "\n" + function + "\n" + """
            poll_delay
            poll_delay
            poll_delay
            printf 'sleeps=%s timers=%s\n' "$sleeps" "$timers"
            """;
        var result = RunExternal(fixture, "/bin/bash", ["-c", harness]);
        Assert.Equal(0, result.ExitCode);
        Assert.Equal("sleeps=1 timers=3\n", Encoding.UTF8.GetString(result.StandardOutput));
    }

    [Theory]
    [InlineData("closed-fd")]
    [InlineData("unexpected-input")]
    [InlineData("partial-no-newline")]
    [InlineData("open-failure")]
    [InlineData("read-failure")]
    [InlineData("mkfifo-failure")]
    public void UnusableFallbackFailsClosed(string fault)
    {
        using var fixture = new ReportSupervisorFixture();
        var setup = fault switch
        {
            "mkfifo-failure" => "mkfifo() { return 73; }\n",
            "open-failure" => "mkfifo() { /bin/mkdir \"$1\"; }\n",
            "read-failure" => "read() { return 73; }\n",
            "closed-fd" => "poll_delay\nexec 8>&-\n",
            "partial-no-newline" => "poll_delay\nprintf 'fragment' >&8\n",
            _ => "poll_delay\nprintf 'unexpected\\n' >&8\n",
        };
        var harness = """
            set -euo pipefail
            TMP_ROOT="$PWD"
            POLL_DELAY_FIFO=''
            POLL_DELAY_FALLBACK=0
            sleep() { return 137; }
            """ + "\n" + PollFunction(fixture) + "\n" + setup + "poll_delay\nprintf 'continued\\n'\n";
        var result = RunExternal(fixture, "/bin/bash", ["-c", harness]);
        Assert.Equal(125, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains("polling delay fallback", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
    }

    [Fact]
    public void FailedDelayPreservesReachedOuterDeadlineAndReleasesSlot()
    {
        WithRun(true, 0, run =>
        {
            run.Start(run.Fixture.ClockEnvironment,
                "STRATALINT_TEST_CLOCK_GATE_FILE=" + run.ReadEntered,
                "PREFLIGHT_DEADLINE_AT=2000000008");
            run.ArmFaultAfterRealWorkerReady();
            run.AwaitReadEntry();
            var stderr = run.Finish(124);
            Assert.True(File.Exists(run.ReadCompleted), "deadline must follow a real timed read completion");
            Assert.Contains("PREFLIGHT_BUDGET_EXHAUSTED owner=outer-deadline", stderr, StringComparison.Ordinal);
            Assert.True(run.Fixture.ClockReads >= 8);
            Assert.False(File.Exists(run.Done));
            run.AssertClean();
        });
    }

    [Theory]
    [InlineData("TERM", 143)]
    [InlineData("HUP", 129)]
    [InlineData("INT", 130)]
    public void FailedDelayPreservesExplicitCancellation(string signal, int expectedExit)
    {
        WithRun(true, 0, run =>
        {
            run.Start();
            run.ArmFaultAfterRealWorkerReady();
            run.AwaitReadEntry();
            var result = run.Fixture.RunExternalProcess("/bin/kill",
                ["-" + signal, run.ProcessId.ToString(CultureInfo.InvariantCulture)]);
            Assert.Equal(0, result.ExitCode);
            run.Finish(expectedExit);
            Assert.True(File.Exists(run.ReadCompleted), "cancellation must leave the real read before cleanup");
            Assert.False(File.Exists(run.Done));
            run.AssertClean();
        });
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void CallerDescriptorSurvivesWorkerLaunchAndOptionalFallback(bool useFallback, bool callerFd8)
    {
        WithRun(true, 7, run =>
        {
            if (!useFallback) run.UseNormalDelay();
            run.Start();
            if (useFallback)
            {
                run.ArmFaultAfterRealWorkerReady();
                run.AwaitReadEntry();
            }
            else run.AwaitWorkerReady();
            run.ReleaseWorker();
            run.Finish(7);
            if (!useFallback) Assert.False(File.Exists(run.ReadEntered));
            run.AssertCallerDescriptor(useFallback);
            run.AssertClean();
        }, callerFd8: callerFd8);
    }

    [Theory]
    [InlineData("HUP", 129)]
    [InlineData("INT", 130)]
    [InlineData("TERM", 143)]
    public void TimedFallbackRestoresCancellationAfterRead(string signal, int expectedExit)
    {
        using var fixture = new ReportSupervisorFixture();
        var harness = """
            set -euo pipefail
            TMP_ROOT="$PWD"
            POLL_DELAY_FIFO=''
            POLL_DELAY_FALLBACK=0
            sleep() { return 137; }
            trap 'exit 129' HUP
            trap 'exit 130' INT
            trap 'exit 143' TERM
            """ + "\n" + PollFunction(fixture) + "\npoll_delay\nkill -" + signal + " \"$$\"\nprintf 'continued\\n'\n";
        var result = RunExternal(fixture, "/bin/bash", ["-c", harness]);
        Assert.Equal(expectedExit, result.ExitCode);
        Assert.Empty(result.StandardOutput);
    }

    [Fact]
    public void UnexpectedEarlyExitFailsWithRealExitAndSanitizedDiagnostics()
    {
        var error = Assert.Throws<InvalidOperationException>(() => WithRun(false, 0, run =>
        {
            run.StartUnexpectedExit();
            run.ArmFaultAfterRealWorkerReady();
        }));
        Assert.Contains("unexpected supervisor exit=73", error.Message, StringComparison.Ordinal);
        Assert.Contains("fixture-error", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("\u001b", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void PartialConstructionFailureIsRetained()
    {
        var original = new InvalidOperationException("constructor control");
        string? allocatedRoot = null;
        var actual = Assert.Throws<InvalidOperationException>(() =>
            new PollRun(false, 0, afterAllocation: fixture =>
            {
                allocatedRoot = fixture.Root;
                throw original;
            }));
        Assert.Same(original, actual);
        Assert.NotNull(allocatedRoot);
        Assert.False(Directory.Exists(allocatedRoot), "partial constructor must dispose its allocated fixture");
    }

    [Fact]
    public void CleanupAttemptsAreIndependentAndKeepOriginalFailure()
    {
        var attempted = new List<int>();
        var original = new InvalidOperationException("original");
        var errors = AttemptAll([
            () => { attempted.Add(1); throw new IOException("cleanup one"); },
            () => { attempted.Add(2); throw new IOException("cleanup two"); },
            () => attempted.Add(3),
        ]);
        var aggregate = Assert.Throws<AggregateException>(() => Rethrow(original, errors));
        Assert.Equal(new[] { 1, 2, 3 }, attempted);
        Assert.Same(original, aggregate.InnerExceptions[0]);
        Assert.Equal(3, aggregate.InnerExceptions.Count);
    }

    private static List<Exception> AttemptAll(IEnumerable<Action> actions)
    {
        var failures = new List<Exception>();
        foreach (var action in actions)
            try { action(); } catch (Exception error) { failures.Add(error); }
        return failures;
    }

    private static void Rethrow(Exception? original, List<Exception> cleanup)
    {
        if (cleanup.Count > 0)
            {
            if (original is not null) cleanup.Insert(0, original);
            throw new AggregateException(cleanup);
        }
        if (original is not null) ExceptionDispatchInfo.Capture(original).Throw();
    }

    private static void WithRun(bool persistent, int workerExit, Action<PollRun> test, bool callerFd8 = false)
    {
        PollRun? run = null;
        Exception? original = null;
        try { run = new PollRun(persistent, workerExit, callerFd8); test(run); }
        catch (Exception error) { original = error is SkipException
            ? new InvalidOperationException("native prerequisite/guard unresolved", error) : error; }
        Rethrow(original, run?.CleanupErrors() ?? []);
    }

    private static string Sanitize(string text)
    {
        var result = new StringBuilder();
        foreach (var c in text.Take(8192))
            result.Append(char.IsControl(c) && c is not '\n' and not '\r' and not '\t' ? '?' : c);
        return result.ToString();
    }

    private static ProcessOutput RunExternal(ReportSupervisorFixture fixture, string name, IEnumerable<string> arguments)
    {
        try { return fixture.RunExternalProcess(name, arguments); }
        catch (SkipException error) { throw new InvalidOperationException("native prerequisite/guard unresolved", error); }
    }

    private static string CopyObservedSupervisor(ReportSupervisorFixture fixture)
    {
        var root = Path.Combine(fixture.Root, "poll-repo");
        var scripts = Path.Combine(root, "tools", "scripts");
        Directory.CreateDirectory(Path.Combine(scripts, "report"));
        Directory.CreateDirectory(Path.Combine(scripts, "lib"));
        foreach (var name in new[] { "resource-observation-lib.sh", "maintenance-log-lib.sh" })
        {
            var source = Path.Combine(fixture.RepositoryRoot, "tools", "scripts", "lib", name);
            if (File.Exists(source)) File.Copy(source, Path.Combine(scripts, "lib", name));
        }
        // Observe the existing finish callback in this disposable copy only.
        File.AppendAllText(Path.Combine(scripts, "lib", "maintenance-log-lib.sh"), "\n" + """
            maintenance_log_finish() {
              if { : <&8; } 2>/dev/null; then
                printf 'inherited\n' > "$PWD/poll-finish-fd8"
              else
                printf 'closed\n' > "$PWD/poll-finish-fd8"
              fi
            }
            """ + "\n");
        var code = File.ReadAllText(fixture.Supervisor);
        _ = PollFunction(fixture); // exact unique marker/current extraction contract
        var hook = """
            read() {
              if [[ "$#" != 8 || "$1" != -r || "$2" != -n || "$3" != 1 || "$4" != -t || "$5" != 1 || "$6" != -u || "$7" != 8 || "$8" != input ]]; then
                builtin read "$@"; return "$?"
              fi
              printf 'entered\n' > "$PWD/poll-read-entered"
              local rc=0
              if builtin read "$@"; then rc=0; else rc=$?; fi
              printf '%s\n' "$rc" > "$PWD/poll-read-completed"
              return "$rc"
            }
            """;
        code = code.Replace("poll_delay() {", hook + "\npoll_delay() {", StringComparison.Ordinal);
        var target = Path.Combine(scripts, "report", "report-supervisor.sh");
        File.WriteAllText(target, code, new UTF8Encoding(false));
        return target;
    }

    private static string PollFunction(ReportSupervisorFixture fixture)
    {
        var source = File.ReadAllText(fixture.Supervisor);
        var start = source.IndexOf("poll_delay() {", StringComparison.Ordinal);
        Assert.True(start >= 0, "production polling-delay repair is missing");
        Assert.Equal(start, source.LastIndexOf("poll_delay() {", StringComparison.Ordinal));
        var end = source.IndexOf("\nfinish() {", start, StringComparison.Ordinal);
        Assert.True(end > start);
        return source[start..end];
    }

    private sealed class PollRun : IDisposable
    {
        internal ReportSupervisorFixture Fixture { get; } = new();
        private Process? process;
        private Task<string>? stdout;
        private Task<string>? stderr;
        private readonly StringBuilder capturedOut = new();
        private readonly StringBuilder capturedErr = new();
        private readonly Dictionary<int, DateTime> ownedPids = [];
        private readonly string worker;
        private readonly string supervisor;
        private readonly bool callerFd8;
        private string At(string name) => Path.Combine(Fixture.Root, name);
        internal string Done => At("poll-worker-done");
        internal string Failed => At("poll-delay-failed");
        internal string ReadEntered => At("poll-read-entered");
        internal string ReadCompleted => At("poll-read-completed");
        internal string SleepCount => At("poll-sleep-count");
        internal int ProcessId => process!.Id;

        internal PollRun(bool persistent, int workerExit, bool callerFd8 = false, Action<ReportSupervisorFixture>? afterAllocation = null)
        {
            try
            {
                this.callerFd8 = callerFd8;
                afterAllocation?.Invoke(Fixture);
                // Existing fixture ps/pgrep are synthetic for its other cases. This
                // case owns real child/grandchild processes and needs the real APIs.
                _ = Fixture.WriteExecutable("ps", "#!/bin/bash\nexec /bin/ps \"$@\"");
                _ = Fixture.WriteExecutable("pgrep", "#!/bin/bash\nexec /usr/bin/pgrep \"$@\"");
                supervisor = CopyObservedSupervisor(Fixture);
                var fifo = Fixture.RunExternalProcess("mkfifo",
                    [At("poll-arm.fifo"), At("poll-release.fifo"), At("poll-grand-release.fifo"), At("poll-grand-ready.fifo")]);
                Assert.Equal(0, fifo.ExitCode);
                _ = Fixture.WriteExecutable("sleep", """
                    #!/bin/bash
                    set -euo pipefail
                    [[ "$*" == 0.1 ]] || exec /bin/sleep "$@"
                    count=0
                    [[ ! -s "$PWD/poll-sleep-count" ]] || read -r count < "$PWD/poll-sleep-count"
                    count=$((count + 1))
                    printf '%s\n' "$count" > "$PWD/poll-sleep-count"
                    if (( count == 1 )); then
                      exec 7<>"$PWD/poll-arm.fifo"
                      printf 'entered\n' > "$PWD/poll-delay-entered"
                      IFS= read -r _ <&7
                    fi
                    if [[ __PERSISTENT__ == 1 || "$count" == 1 ]]; then
                      printf 'failed\n' > "$PWD/poll-delay-failed"
                      exit 137
                    fi
                    exec /bin/sleep "$@"
                    """.Replace("__PERSISTENT__", persistent ? "1" : "0", StringComparison.Ordinal));
                var grand = Fixture.WriteExecutable("poll-grand.sh", """
                    #!/bin/bash
                    set -euo pipefail
                    exec 6<>"$PWD/poll-grand-release.fifo"
                    printf 'ready\n' > "$PWD/poll-grand-ready.fifo"
                    IFS= read -r _ <&6
                    """);
                worker = Fixture.WriteExecutable("poll-worker.sh", """
                    #!/bin/bash
                    set -euo pipefail
                    child=''
                    cleanup_child() {
                      [[ -z "$child" ]] || kill -TERM "$child" 2>/dev/null || true
                      [[ -z "$child" ]] || wait "$child" 2>/dev/null || true
                    }
                    trap cleanup_child EXIT
                    trap 'exit 143' TERM
                    trap 'exit 129' HUP
                    printf '%s\n' "$$" > "$PWD/poll-worker.pid"
                    if { : <&8; } 2>/dev/null; then
                      printf 'inherited\n' > "$PWD/poll-fd8"
                    else
                      printf 'closed\n' > "$PWD/poll-fd8"
                    fi
                    fallback=absent
                    for timer in "$STRATALINT_SUPERVISOR_ROOT"/runs/*/poll-delay.fifo; do
                      if [[ -p "$timer" ]]; then fallback=present; fi
                    done
                    printf '%s\n' "$fallback" > "$PWD/poll-fallback-before-worker"
                    exec 7<>"$PWD/poll-release.fifo"
                    /bin/bash "$PWD/poll-grand.sh" &
                    child=$!
                    printf '%s\n' "$child" > "$PWD/poll-grand.pid"
                    IFS= read -r _ < "$PWD/poll-grand-ready.fifo"
                    printf 'ready\n' > "$PWD/poll-worker-ready"
                    IFS= read -r _ <&7
                    if { : <&8; } 2>/dev/null; then
                      printf 'after-launch\n' >&8
                      printf 'inherited\n' > "$PWD/poll-fd8-after"
                    else
                      printf 'closed\n' > "$PWD/poll-fd8-after"
                    fi
                    printf '__EXIT__\n' > "$PWD/poll-worker-done"
                    exit __EXIT__
                    """.Replace("__EXIT__", workerExit.ToString(CultureInfo.InvariantCulture), StringComparison.Ordinal));
                _ = grand;
            }
            catch (Exception original)
            {
                var cleanup = CleanupErrors();
                if (cleanup.Count > 0) throw new AggregateException(new[] { original }.Concat(cleanup));
                throw;
            }
        }

        internal void UseNormalDelay() =>
            _ = Fixture.WriteExecutable("sleep", "#!/bin/bash\nexec /bin/sleep \"$@\"\n");

        internal void StartUnexpectedExit()
        {
            File.WriteAllText(supervisor, "#!/bin/bash\nprintf 'fixture-error\\033[31m\\n' >&2\nexit 73\n");
            Start();
        }

        internal void Start(params string[] environment)
        {
            // Same env/process contract as ReportSupervisorFixture, with an
            // explicit Bash 3.2 invocation on macOS. No BASH_ENV injection.
            var info = new ProcessStartInfo
            {
                FileName = "env", WorkingDirectory = Fixture.Root, UseShellExecute = false,
                RedirectStandardOutput = true, RedirectStandardError = true,
            };
            foreach (var value in new[]
            {
                $"PATH={Fixture.Root}:{Fixture.HostPath}",
                $"STRATALINT_SUPERVISOR_ROOT={Fixture.StateRoot}",
                "STRATALINT_LEAN_MAX_CONCURRENCY=1", "STRATALINT_LOCK_TIMEOUT_SECONDS=86400",
                "STRATALINT_BUILD_TIMEOUT_SECONDS=60", "PREFLIGHT_DEADLINE_AT=",
            }) info.ArgumentList.Add(value);
            foreach (var value in environment) info.ArgumentList.Add(value);
            info.ArgumentList.Add("/bin/bash");
            info.ArgumentList.Add("-c");
            // Open (or explicitly close) the caller descriptor before the real
            // supervisor starts. Fallback still opens only after worker launch.
            info.ArgumentList.Add(callerFd8
                ? "exec 8>\"$1\"; shift; exec /bin/bash \"$@\""
                : "exec 8>&-; shift; exec /bin/bash \"$@\"");
            info.ArgumentList.Add("--");
            info.ArgumentList.Add(At("poll-caller-fd8"));
            foreach (var value in new[] { supervisor, "--role", "lean-producer", "--lean-slot", "--", worker })
                info.ArgumentList.Add(value);
            process = new Process { StartInfo = info };
            Assert.True(process.Start());
            stdout = CaptureAsync(process.StandardOutput, capturedOut);
            stderr = CaptureAsync(process.StandardError, capturedErr);
        }

        private void Await(Func<bool> condition, string boundary)
        {
            Wait(() => condition() || process!.HasExited, boundary);
            if (!condition())
            {
                _ = SpinWait.SpinUntil(() => (stdout?.IsCompleted ?? true) && (stderr?.IsCompleted ?? true), Fixture.SafetyTimeout);
                throw new InvalidOperationException("unexpected supervisor exit="
                    + process!.ExitCode.ToString(CultureInfo.InvariantCulture)
                    + " before " + boundary + Diagnostics());
            }
        }

        private void Wait(Func<bool> condition, string boundary)
        {
            if (!SpinWait.SpinUntil(condition, Fixture.SafetyTimeout))
                throw new TimeoutException("unresolved test guard: " + boundary + Diagnostics());
        }

        private static async Task<string> CaptureAsync(StreamReader reader, StringBuilder capture)
        {
            var chunk = new char[1024];
            int count;
            while ((count = await reader.ReadAsync(chunk.AsMemory())) > 0)
                lock (capture)
                    capture.Append(chunk, 0, Math.Min(count, Math.Max(0, 8192 - capture.Length)));
            lock (capture) return capture.ToString();
        }

        private string Diagnostics()
        {
            string Snapshot(StringBuilder buffer)
            {
                lock (buffer) return Sanitize(buffer.ToString()).Replace(Fixture.Root, "<fixture>", StringComparison.Ordinal);
            }
            return "; stdout=" + Snapshot(capturedOut) + "; stderr=" + Snapshot(capturedErr)
                + "; captures_complete=" + ((stdout?.IsCompleted ?? false) && (stderr?.IsCompleted ?? false));
        }

        internal void AwaitReadEntry()
        {
            Await(() => File.Exists(ReadEntered), "real builtin timed-read call entry");
            Await(() =>
            {
                var state = RunExternal(Fixture, "/bin/ps",
                    ["-o", "stat=", "-p", ProcessId.ToString(CultureInfo.InvariantCulture)]);
                return state.ExitCode == 0 && Encoding.UTF8.GetString(state.StandardOutput).TrimStart()
                    .StartsWith("S", StringComparison.Ordinal) && !File.Exists(ReadCompleted);
            }, "sleeping supervisor within real-read call window");
            // This is an observable call-window handshake, not syscall tracing.
            Assert.False(File.Exists(ReadCompleted), "signal case missed the blocking read window");
        }

        internal void AwaitWorkerReady()
        {
            Await(() => File.Exists(At("poll-worker-ready")), "real worker.ready");
            foreach (var name in new[] { "poll-worker.pid", "poll-grand.pid" })
            {
                var pid = int.Parse(File.ReadAllText(At(name)).Trim(), CultureInfo.InvariantCulture);
                using var owned = Process.GetProcessById(pid);
                ownedPids[pid] = owned.StartTime;
                Assert.True(ProcessExists(pid));
            }
            Assert.Equal("absent", File.ReadAllText(At("poll-fallback-before-worker")).Trim());
            Assert.Equal(callerFd8 ? "inherited" : "closed", File.ReadAllText(At("poll-fd8")).Trim());
        }

        internal void AssertCallerDescriptor(bool useFallback)
        {
            Assert.Equal(callerFd8 ? "inherited" : "closed", File.ReadAllText(At("poll-fd8-after")).Trim());
            if (callerFd8) Assert.Equal("after-launch\n", File.ReadAllText(At("poll-caller-fd8")));
            Assert.Equal(!useFallback && callerFd8 ? "inherited" : "closed",
                File.ReadAllText(At("poll-finish-fd8")).Trim());
        }

        internal void ArmFaultAfterRealWorkerReady()
        {
            AwaitWorkerReady();
            Assert.Single(Directory.GetDirectories(Path.Combine(Fixture.StateRoot, "slots"), "slot-*.lock"));
            Await(() => File.Exists(At("poll-delay-entered")), "polling delay entry");
            Send("poll-arm.fifo");
            Await(() => File.Exists(Failed), "injected sleep failure");
        }

        private void Send(string name)
        {
            var result = Fixture.RunExternalProcess("/bin/bash",
                ["-c", "exec 7<>\"$1\"; printf 'release\\n' >&7", "--", At(name)]);
            Assert.Equal(0, result.ExitCode);
        }

        internal void ReleaseWorker() => Send("poll-release.fifo");

        internal string Finish(int exit)
        {
            Wait(() => process!.HasExited, "supervisor/worker did not finish");
            Wait(() => stdout!.IsCompleted && stderr!.IsCompleted, "supervisor relay EOF");
            Assert.True(exit == process!.ExitCode, "expected supervisor exit=" + exit
                + "; actual=" + process.ExitCode + Diagnostics());
            return stderr!.GetAwaiter().GetResult();
        }

        internal void AssertClean()
        {
            Wait(() => ownedPids.Keys.All(pid => !ProcessExists(pid)), "owned worker tree survived cleanup");
            Assert.Empty(Directory.GetDirectories(Path.Combine(Fixture.StateRoot, "slots"), "slot-*.lock"));
            Assert.Empty(Directory.GetDirectories(Path.Combine(Fixture.StateRoot, "runs")));
        }

        internal List<Exception> CleanupErrors()
        {
            var actions = new List<Action>();
            if (process is not null)
            {
                actions.Add(() => { if (!process.HasExited) process.Kill(entireProcessTree: true); });
                actions.Add(() => Wait(() => process.HasExited, "join supervisor during cleanup"));
            }
            // Recover pid files even if readiness/identity capture failed midway.
            foreach (var name in new[] { "poll-worker.pid", "poll-grand.pid" })
                actions.Add(() =>
                {
                    if (File.Exists(At(name)) && int.TryParse(File.ReadAllText(At(name)).Trim(), out var pid)
                        && !ownedPids.ContainsKey(pid))
                    {
                        try { using var p = Process.GetProcessById(pid); ownedPids[pid] = p.StartTime; }
                        catch (ArgumentException) { }
                    }
                });
            actions.Add(() =>
            {
                var errors = new List<Exception>();
                foreach (var (pid, start) in ownedPids)
                    try
                    {
                        using var owned = Process.GetProcessById(pid);
                        if (!owned.HasExited && owned.StartTime == start) owned.Kill(entireProcessTree: true);
                    }
                    catch (ArgumentException) { }
                    catch (Exception error) { errors.Add(error); }
                if (errors.Count > 0) throw new AggregateException(errors);
            });
            actions.Add(() => Wait(() => ownedPids.Keys.All(pid => !ProcessExists(pid)), "join worker tree during cleanup"));
            if (stdout is not null || stderr is not null)
                actions.Add(() => Wait(() => (stdout?.IsCompleted ?? true) && (stderr?.IsCompleted ?? true), "relay EOF during cleanup"));
            actions.Add(() => process?.Dispose());
            actions.Add(Fixture.Dispose);
            return AttemptAll(actions);
        }

        public void Dispose()
        {
            var failures = CleanupErrors();
            if (failures.Count > 0) throw new AggregateException(failures);
        }

        private static bool ProcessExists(int pid)
        {
            if (Directory.Exists("/proc"))
            {
                try
                {
                    var stat = File.ReadAllText(Path.Combine("/proc", pid.ToString(CultureInfo.InvariantCulture), "stat"));
                    var end = stat.LastIndexOf(')');
                    if (end >= 0 && end + 2 < stat.Length && stat[end + 2] is 'Z' or 'X') return false;
                }
                catch (FileNotFoundException) { return false; }
                catch (DirectoryNotFoundException) { return false; }
            }
            try
            {
                using var p = Process.GetProcessById(pid);
                return !p.HasExited && (Directory.Exists("/proc") || p.Threads.Count > 0);
            }
            catch (ArgumentException) { return false; }
        }
    }
}
