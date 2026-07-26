using System.Diagnostics;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    private sealed class DeadOwnerObservationFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal DeadOwnerObservationFixture()
        {
            _ = WriteExecutable("restore-clock.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                /bin/ln -sf /bin/date "$1.next"
                /bin/mv -f -- "$1.next" "$1"
                """);
            SuccessWorker = WriteExecutable("success.sh", "#!/usr/bin/env bash\nexit 0");
            SleepWorker = WriteExecutable("sleep.sh", """
                #!/usr/bin/env bash
                printf '%s\n' "$$" > "$1/sleep-worker.pid"
                exec sleep 60
                """);
            OleanProgressWorker = WriteExecutable("olean-progress.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                mkdir -p "$1/.lake/build/lib/lean"
                for index in 1 2 3 4; do
                  touch "$1/.lake/build/lib/lean/progress-${index}.olean"
                  sleep 1
                done
                "$1/restore-clock.sh" "$1/clock-bin/date"
                """);
            PipeProgressWorker = WriteExecutable("pipe-progress.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                for index in 1 2 3 4; do
                  printf 'progress-%s\n' "$index"
                  sleep 1
                done
                "$1/restore-clock.sh" "$1/clock-bin/date"
                """);
            LogProgressWorker = WriteExecutable("log-progress.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                mkdir -p "$STRATALINT_LEAN_PROGRESS_LOG_ROOT"
                for index in 1 2 3 4; do
                  printf 'progress-%s\n' "$index" >> "$STRATALINT_LEAN_PROGRESS_LOG_ROOT/build.stdout.log"
                  sleep 1
                done
                "$1/restore-clock.sh" "$1/clock-bin/date"
                """);
            CpuOnlyWorker = WriteExecutable("cpu-only.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                perl -MTime::HiRes=time -e '$end = time() + 5; 1 while time() < $end'
                "$1/restore-clock.sh" "$1/clock-bin/date"
                """);
            QuantizedLowDutyWorker = WriteExecutable("quantized-low-duty.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                sleep 5
                "$1/restore-clock.sh" "$1/clock-bin/date"
                """);
            File.WriteAllText(ClosedFdDescendantHoldFile, string.Empty, new UTF8Encoding(false));
            ClosedFdDescendantWorker = WriteExecutable("closed-fd-descendant.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                printf '%s\n' "$$" > "$1/closed-fd-leader.pid"
                (
                  trap '' TERM
                  exec 9<&- >/dev/null 2>&1
                  while [[ -e "$1/closed-fd-descendant.hold" ]]; do sleep 0.05; done
                ) &
                descendant_pid=$!
                printf '%s\n' "$descendant_pid" > "$1/closed-fd-descendant.pid"
                wait "$descendant_pid"
                """);
            _ = WriteExecutable("ps", """
                #!/usr/bin/env bash
                if [[ "${STRATALINT_TEST_PS_FAIL_ALL:-}" == "1" ]]; then exit 1; fi
                if [[ "${STRATALINT_TEST_PS_MALFORMED_TABLE:-}" == "1" && "$*" == *"pid=,pgid=,stat="* ]]; then
                  printf 'malformed-successful-row\n'
                  exit 0
                fi
                if [[ -n "${STRATALINT_TEST_PS_DEAD_GROUP_STATE:-}" && "$*" == *"pid=,pgid=,stat="* ]]; then
                  printf '424242 99999999 %s\n' "$STRATALINT_TEST_PS_DEAD_GROUP_STATE"
                  exit 0
                fi
                if [[ "${STRATALINT_TEST_QUANTIZED_CPU:-}" == "1" && "$*" == *"time="* ]]; then
                  value=0
                  if [[ -f "$STRATALINT_TEST_CLOCK_FILE" ]]; then read -r value < "$STRATALINT_TEST_CLOCK_FILE"; fi
                  seconds=$((value / 60))
                  printf '%02d:%02d:%02d\n' $((seconds / 3600)) $(((seconds / 60) % 60)) $((seconds % 60))
                  exit 0
                fi
                previous=""
                requested_pid=""
                for argument in "$@"; do
                  if [[ "$previous" == "-p" ]]; then requested_pid="$argument"; fi
                  if [[ "$previous" == "-p" && "$argument" == "${STRATALINT_TEST_PS_REUSED_PID:-}" ]]; then
                    printf 'synthetic-current-start\n'
                    exit 0
                  fi
                  if [[ "$previous" == "-p" && "$argument" == "${STRATALINT_TEST_PS_FAIL_PID:-}" ]]; then
                    exit 1
                  fi
                  previous="$argument"
                done
                if [[ "$*" == *"lstart="* ]]; then
                  printf 'synthetic-start-%s\n' "$requested_pid"
                  exit 0
                fi
                if [[ "$*" == *"pid=,pgid=,stat="* ]]; then
                  pid=""
                  group=""
                  if [[ -n "${STRATALINT_TEST_GROUP_MEMBER_PID_FILE:-}" \
                    && -s "$STRATALINT_TEST_GROUP_MEMBER_PID_FILE" ]]; then
                    read -r pid < "$STRATALINT_TEST_GROUP_MEMBER_PID_FILE"
                  fi
                  group_record="${STRATALINT_TEST_GROUP_RECORD:-}"
                  if [[ -z "$group_record" && -n "${STRATALINT_SUPERVISOR_ROOT:-}" ]]; then
                    group_record="$STRATALINT_SUPERVISOR_ROOT/slots/slot-1.lock/group"
                  fi
                  if [[ -s "$group_record" ]]; then
                    IFS='|' read -r group _ < "$group_record"
                    if [[ -z "$pid" ]]; then
                      IFS='|' read -r _ pid _ < "$group_record"
                    fi
                  fi
                  running=0
                  if [[ "$pid" =~ ^[1-9][0-9]*$ && "$group" =~ ^[1-9][0-9]*$ ]] \
                    && kill -0 "$pid" 2>/dev/null; then
                    running=1
                    if [[ -r "/proc/$pid/stat" ]]; then
                      stat="$(< "/proc/$pid/stat")"
                      suffix="${stat##*) }"
                      state="${suffix%% *}"
                      [[ "$state" == "Z" || "$state" == "X" ]] && running=0
                    fi
                  fi
                  if [[ "$running" == "1" ]]; then
                    printf '%s %s S\n' "$pid" "$group"
                  else
                    printf '1 1 S\n'
                  fi
                  exit 0
                fi
                if [[ "$*" == *"stat="* ]]; then printf 'S\n'; exit 0; fi
                if [[ "$*" == *"time="* ]]; then printf '00:00:00\n'; exit 0; fi
                if [[ "$*" == *"rss="* ]]; then printf '0\n'; exit 0; fi
                exit 1
                """);
            _ = WriteExecutable(Path.Combine("clock-bin", "date"), """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "$*" != "+%s" || -z "${STRATALINT_TEST_CLOCK_FILE:-}" ]]; then
                  exec /bin/date "$@"
                fi
                value=0
                if [[ -f "$STRATALINT_TEST_CLOCK_FILE" ]]; then read -r value < "$STRATALINT_TEST_CLOCK_FILE"; fi
                value=$((value + ${STRATALINT_TEST_CLOCK_STEP_SECONDS:-1}))
                printf '%s\n' "$value" > "$STRATALINT_TEST_CLOCK_FILE"
                printf '%s\n' "$value"
                """);
        }

        internal string Root => temporary.Path;
        internal string StateRoot => Path.Combine(Root, "state");
        internal string MetricsLog => Path.Combine(Root, "metrics.jsonl");
        internal string Slot => Path.Combine(StateRoot, "slots", "slot-1.lock");
        internal string ProgressLogRoot => Path.Combine(Root, "producer.logs");
        internal string SleepWorkerPidFile => Path.Combine(Root, "sleep-worker.pid");
        internal string ClosedFdLeaderPidFile => Path.Combine(Root, "closed-fd-leader.pid");
        internal string ClosedFdDescendantPidFile => Path.Combine(Root, "closed-fd-descendant.pid");
        internal string ClosedFdDescendantHoldFile => Path.Combine(Root, "closed-fd-descendant.hold");
        internal string ObservationClockFile => Path.Combine(Root, "observation.clock");
        internal string ProcessFsRoot => Path.Combine(Root, "proc");
        internal string ClockBin => Path.Combine(Root, "clock-bin");
        internal string HostPath => Environment.GetEnvironmentVariable("PATH") ?? "/bin:/usr/bin";
        internal string SuccessWorker { get; }
        internal string SleepWorker { get; }
        internal string OleanProgressWorker { get; }
        internal string PipeProgressWorker { get; }
        internal string LogProgressWorker { get; }
        internal string CpuOnlyWorker { get; }
        internal string QuantizedLowDutyWorker { get; }
        internal string ClosedFdDescendantWorker { get; }

        internal bool SlotExists() => Directory.Exists(Slot);

        internal bool SlotMetadataIsPublished() =>
            File.Exists(Path.Combine(Slot, "marker"))
            && File.Exists(Path.Combine(Slot, "group"));

        internal int ReadSleepWorkerPid() => int.Parse(
            File.ReadAllText(SleepWorkerPidFile).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        internal int ReadPid(string path) => int.Parse(
            File.ReadAllText(path).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        internal (int GroupId, int LeaderPid) ReadProcessGroup()
        {
            var fields = File.ReadAllText(Path.Combine(Slot, "group")).Trim().Split('|');
            Assert.Equal(3, fields.Length);
            return (
                int.Parse(fields[0], System.Globalization.CultureInfo.InvariantCulture),
                int.Parse(fields[1], System.Globalization.CultureInfo.InvariantCulture));
        }

        internal void KillProcess(int pid)
        {
            var result = BoundedProcessRunner.Run(
                "/bin/kill",
                ["-KILL", pid.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                Root,
                TimeSpan.FromSeconds(5),
                4096);
            Assert.Equal(0, result.ExitCode);
        }

        internal string CreateSlotOwnedByCurrentProcess()
        {
            Directory.CreateDirectory(Slot);
            if (Directory.Exists("/proc"))
            {
                File.WriteAllText(
                    Path.Combine(Slot, "owner"),
                    $"{Environment.ProcessId}|{EmptyGroupLeaderStartIdentity()}\n",
                    new UTF8Encoding(false));
                return Slot;
            }
            var start = BoundedProcessRunner.Run(
                Path.Combine(Root, "ps"),
                ["-o", "lstart=", "-p", Environment.ProcessId.ToString(
                    System.Globalization.CultureInfo.InvariantCulture)],
                Root,
                TimeSpan.FromSeconds(5),
                4096);
            Assert.Equal(0, start.ExitCode);
            File.WriteAllText(
                Path.Combine(Slot, "owner"),
                $"{Environment.ProcessId}|{Encoding.UTF8.GetString(start.StandardOutput).Trim()}\n",
                new UTF8Encoding(false));
            return Slot;
        }

        internal void CreateTimestampedSlotOwnedByCurrentProcess(long timestamp)
        {
            _ = CreateSlotOwnedByCurrentProcess();
            var ownerFile = Path.Combine(Slot, "owner");
            var owner = File.ReadAllText(ownerFile).Trim();
            File.WriteAllText(
                ownerFile,
                $"{owner}|{timestamp}\n",
                new UTF8Encoding(false));
        }

        internal string CreateSlotWithOwner(string owner)
        {
            Directory.CreateDirectory(Slot);
            File.WriteAllText(Path.Combine(Slot, "owner"), owner, new UTF8Encoding(false));
            return Slot;
        }

        internal string AttachEmptyProcessGroup()
        {
            var marker = Path.Combine(Root, "synthetic-process.marker");
            File.WriteAllText(marker, string.Empty, new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(Slot, "marker"),
                marker + "\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(Slot, "group"),
                $"99999999|99999999|{EmptyGroupLeaderStartIdentity()}\n",
                new UTF8Encoding(false));
            return marker;
        }

        internal void AttachSyntheticMarkerDescriptor(int pid, int descriptor, string marker)
        {
            var fdRoot = Path.Combine(
                ProcessFsRoot,
                pid.ToString(System.Globalization.CultureInfo.InvariantCulture),
                "fd");
            Directory.CreateDirectory(fdRoot);
            File.CreateSymbolicLink(
                Path.Combine(fdRoot, descriptor.ToString(
                    System.Globalization.CultureInfo.InvariantCulture)),
                marker);
        }

        internal void AttachSyntheticProcStat(
            int pid,
            char state,
            int parentPid = 1,
            int? processGroupId = null,
            long starttime = 12345)
        {
            var processRoot = Path.Combine(
                ProcessFsRoot,
                pid.ToString(System.Globalization.CultureInfo.InvariantCulture));
            Directory.CreateDirectory(processRoot);
            var suffix = Enumerable.Repeat("0", 20).ToArray();
            suffix[0] = state.ToString();
            suffix[1] = parentPid.ToString(System.Globalization.CultureInfo.InvariantCulture);
            suffix[2] = (processGroupId ?? pid).ToString(
                System.Globalization.CultureInfo.InvariantCulture);
            suffix[19] = starttime.ToString(System.Globalization.CultureInfo.InvariantCulture);
            File.WriteAllText(
                Path.Combine(processRoot, "stat"),
                $"{pid} (worker with ) paren) {string.Join(' ', suffix)}\n",
                new UTF8Encoding(false));
        }

        internal void AttachMalformedSyntheticProcStat(int pid)
        {
            var processRoot = Path.Combine(
                ProcessFsRoot,
                pid.ToString(System.Globalization.CultureInfo.InvariantCulture));
            Directory.CreateDirectory(processRoot);
            File.WriteAllText(
                Path.Combine(processRoot, "stat"),
                $"{pid} malformed\n",
                new UTF8Encoding(false));
        }

        internal void AttachUnreadableSyntheticProcStat(int pid)
        {
            var processRoot = Path.Combine(
                ProcessFsRoot,
                pid.ToString(System.Globalization.CultureInfo.InvariantCulture));
            Directory.CreateDirectory(Path.Combine(processRoot, "stat"));
        }

        internal string[] AcceleratedObservationEnvironment(int stepSeconds) =>
        [
            $"PATH={ClockBin}:{Root}:{HostPath}",
            $"STRATALINT_TEST_CLOCK_FILE={ObservationClockFile}",
            $"STRATALINT_TEST_CLOCK_STEP_SECONDS={stepSeconds}",
            "STRATALINT_REPORT_STALL_WINDOW_SECONDS=60",
            "STRATALINT_REPORT_STALL_WINDOW_COUNT=3",
        ];

        internal string[] SyntheticProcessEnvironment(string pidFile, int lockTimeoutSeconds) =>
        [
            $"PATH={Root}:{HostPath}",
            $"STRATALINT_TEST_GROUP_MEMBER_PID_FILE={pidFile}",
            $"STRATALINT_TEST_GROUP_RECORD={Path.Combine(Slot, "group")}",
            $"STRATALINT_LOCK_TIMEOUT_SECONDS={lockTimeoutSeconds}",
        ];

        internal ProcessOutput Run(string worker, params string[] environment) =>
            BoundedProcessRunner.Run(
                "env",
                Arguments(worker, environment),
                Root,
                TimeSpan.FromSeconds(12),
                1024 * 1024);

        internal ProcessOutput RunMarkerScan(string marker, params int[] candidatePids) =>
            BoundedProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "set -euo pipefail; PROCESS_FS_ROOT=\"$1\"; source \"$2\"; marker_processes_for_path \"$3\" \"$4\"",
                    "marker-scan",
                    ProcessFsRoot,
                    ProcessControl,
                    marker,
                    string.Join(' ', candidatePids),
                ],
                Root,
                TimeSpan.FromSeconds(5),
                4096);

        internal ProcessOutput RunProcessStartIdentity(int pid) =>
            BoundedProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "set -euo pipefail; PROCESS_FS_ROOT=\"$1\"; source \"$2\"; process_start_identity \"$3\"",
                    "process-start-identity",
                    ProcessFsRoot,
                    ProcessControl,
                    pid.ToString(System.Globalization.CultureInfo.InvariantCulture),
                ],
                Root,
                TimeSpan.FromSeconds(5),
                4096);

        internal ProcessOutput RunLinuxProcStatSnapshot(int pid) =>
            BoundedProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "set -euo pipefail; PROCESS_FS_ROOT=\"$1\"; source \"$2\"; linux_proc_stat_snapshot \"$3\"",
                    "linux-proc-stat-snapshot",
                    ProcessFsRoot,
                    ProcessControl,
                    pid.ToString(System.Globalization.CultureInfo.InvariantCulture),
                ],
                Root,
                TimeSpan.FromSeconds(5),
                4096);

        internal ProcessOutput RunProcessGroupMembersFromProc(int groupId) =>
            BoundedProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "set -euo pipefail; PROCESS_FS_ROOT=\"$1\"; source \"$2\"; process_group_members_for_id \"$3\"",
                    "process-group-members-proc",
                    ProcessFsRoot,
                    ProcessControl,
                    groupId.ToString(System.Globalization.CultureInfo.InvariantCulture),
                ],
                Root,
                TimeSpan.FromSeconds(5),
                4096);

        internal ProcessOutput RunLinuxProcessCandidates(int groupId, long leaderStarttime) =>
            BoundedProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "set -euo pipefail; PROCESS_FS_ROOT=\"$1\"; source \"$2\"; linux_process_candidates \"$3\" \"$4\"",
                    "linux-process-candidates",
                    ProcessFsRoot,
                    ProcessControl,
                    groupId.ToString(System.Globalization.CultureInfo.InvariantCulture),
                    leaderStarttime.ToString(System.Globalization.CultureInfo.InvariantCulture),
                ],
                Root,
                TimeSpan.FromSeconds(5),
                4096);

        internal ProcessOutput RunFallbackProcessGroupMembers(int groupId) =>
            BoundedProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={Root}:{HostPath}",
                    "STRATALINT_TEST_PS_MALFORMED_TABLE=1",
                    "/bin/bash",
                    "-c",
                    "set -euo pipefail; PROCESS_FS_ROOT=\"$1\"; source \"$2\"; process_group_members_for_id \"$3\"",
                    "fallback-process-group-members",
                    Path.Combine(Root, "missing-procfs"),
                    ProcessControl,
                    groupId.ToString(System.Globalization.CultureInfo.InvariantCulture),
                ],
                Root,
                TimeSpan.FromSeconds(5),
                4096);

        internal ProcessOutput RunProcessExists(int pid) =>
            BoundedProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "set -euo pipefail; PROCESS_FS_ROOT=\"$1\"; source \"$2\"; process_exists \"$3\"",
                    "process-exists",
                    ProcessFsRoot,
                    ProcessControl,
                    pid.ToString(System.Globalization.CultureInfo.InvariantCulture),
                ],
                Root,
                TimeSpan.FromSeconds(5),
                4096);

        internal Process Start(string worker, params string[] environment)
        {
            var info = new ProcessStartInfo
            {
                FileName = "env",
                WorkingDirectory = Root,
                UseShellExecute = false,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
            };
            foreach (var argument in Arguments(worker, environment)) info.ArgumentList.Add(argument);
            var process = new Process { StartInfo = info };
            Assert.True(process.Start());
            return process;
        }

        public void Dispose()
        {
            if (File.Exists(SleepWorkerPidFile)
                && int.TryParse(File.ReadAllText(SleepWorkerPidFile).Trim(), out var workerPid))
            {
                _ = BoundedProcessRunner.Run(
                    "/bin/kill", ["-KILL", $"-{workerPid}"],
                    Root, TimeSpan.FromSeconds(5), 4096);
            }
            if (File.Exists(ClosedFdDescendantPidFile)
                && int.TryParse(File.ReadAllText(ClosedFdDescendantPidFile).Trim(), out var descendantPid))
            {
                _ = BoundedProcessRunner.Run(
                    "/bin/kill", ["-KILL", descendantPid.ToString(
                        System.Globalization.CultureInfo.InvariantCulture)],
                    Root, TimeSpan.FromSeconds(5), 4096);
            }
            if (Directory.Exists(StateRoot))
            {
                foreach (var ownerFile in Directory.GetFiles(StateRoot, "owner", SearchOption.AllDirectories))
                {
                    var owner = File.ReadAllText(ownerFile).Split('|')[0];
                    if (int.TryParse(owner, out var pid) && pid != Environment.ProcessId)
                    {
                        _ = BoundedProcessRunner.Run(
                            "/bin/kill", ["-KILL", pid.ToString(
                                System.Globalization.CultureInfo.InvariantCulture)],
                            Root, TimeSpan.FromSeconds(5), 4096);
                    }
                }
            }
            temporary.Dispose();
        }

        private IReadOnlyList<string> Arguments(string worker, IReadOnlyList<string> environment)
        {
            var arguments = new List<string>
            {
                $"PATH={Root}:{HostPath}",
                $"STRATALINT_REPORT_METRICS_LOG={MetricsLog}",
                $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
                $"STRATALINT_LEAN_PROGRESS_ROOT={Root}",
                $"STRATALINT_LEAN_PROGRESS_LOG_ROOT={ProgressLogRoot}",
                "STRATALINT_BUILD_TIMEOUT_SECONDS=0",
                "STRATALINT_REPORT_OBSERVATION_POLL_SECONDS=1",
            };
            arguments.AddRange(environment);
            arguments.Add(Supervisor);
            arguments.Add("--role");
            arguments.Add("lean-producer");
            arguments.Add("--lean-slot");
            arguments.Add("--");
            arguments.Add(worker);
            arguments.Add(Root);
            return arguments;
        }

        private static string Supervisor => Path.Combine(
            FindRepositoryRoot(), "Meta", "StrataLint", "scripts", "report", "report-supervisor.sh");

        private static string ProcessControl => Path.Combine(
            FindRepositoryRoot(), "Meta", "StrataLint", "scripts", "report", "report-process-control.sh");

        private string WriteExecutable(string name, string contents)
        {
            var path = Path.Combine(Root, name);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, contents + "\n", new UTF8Encoding(false));
            var chmod = BoundedProcessRunner.Run(
                "/bin/chmod", ["+x", path], Root, TimeSpan.FromSeconds(5), 4096);
            Assert.Equal(0, chmod.ExitCode);
            return path;
        }

        private static string FindRepositoryRoot()
        {
            for (var current = new DirectoryInfo(AppContext.BaseDirectory);
                 current is not null;
                 current = current.Parent)
            {
                if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
            }
            throw new DirectoryNotFoundException("Could not locate repository root.");
        }
    }
}
