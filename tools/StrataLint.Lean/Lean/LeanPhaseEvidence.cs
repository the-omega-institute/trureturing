using System.Globalization;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

// Observation for the cache writer's actual native processes. It never supplies
// a build verdict. The original runner owns budgets, output and exceptions.
internal sealed class LeanPhaseEvidence(IWorktreeProcessRunner runner, string lake, TimeProvider clock)
    : IWorktreeProcessRunner
{
    internal const string SupportedVersion = "Lake version 5.0.0-src+d8b1897 (Lean version 4.33.0)";
    internal string Scope { get; set; } = "cache-preparation";
    internal string? Version { get; private set; }
    internal StringBuilder Records { get; } = new();

    internal void ProbeVersion(string root)
    {
        // with-cache-writer also accepts arbitrary commands: do not run them a
        // second time to query a version. An unrecognized executable stays unknown.
        if (Path.GetFileName(lake) != "lake") return;
        try
        {
            var result = runner.Run(lake, ["--version"], root, BoundedProcessRunner.HangDetectionBudget);
            if (result.ExitCode == 0) Version = Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }
        catch (Exception) { /* Version evidence is optional, execution is not. */ }
    }

    internal CommandResult Prepare(string root, Func<CommandResult> prepare)
    {
        var start = Start();
        CommandResult? result = null;
        try { return result = prepare(); }
        finally
        {
            Record("cache-preparation-total", "lean-cache-writer", [], root, start,
                result is null ? null : new ProcessOutput(result.ExitCode ?? (result.Success ? 0 : 2), [], []),
                fullStatuses: false, process: false);
        }
    }

    public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout)
    {
        var fullStatuses = Scope == "lake-build" && Version == SupportedVersion && arguments.SequenceEqual(["build"]);
        IReadOnlyList<string> effective = fullStatuses
            ? ["--verbose", "--log-level=info", "--no-ansi", "build"] : arguments;
        var start = Start();
        ProcessOutput? result = null;
        try { return result = runner.Run(fileName, effective, workingDirectory, timeout); }
        finally { Record(Scope, fileName, effective, workingDirectory, start, result, fullStatuses, process: true); }
    }

    public StreamedProcessOutput<T> RunStreaming<T>(string fileName, IReadOnlyList<string> arguments,
        string workingDirectory, TimeSpan timeout, Func<Stream, CancellationToken, Task<T>> readStandardOutput)
    {
        var start = Start();
        StreamedProcessOutput<T>? result = null;
        try { return result = runner.RunStreaming(fileName, arguments, workingDirectory, timeout, readStandardOutput); }
        finally
        {
            Record(Scope, fileName, arguments, workingDirectory, start,
                result is null ? null : new ProcessOutput(result.ExitCode, [], []), false, process: true);
        }
    }

    private (long? Tick, DateTimeOffset? Utc) Start()
    {
        try { return (clock.GetTimestamp(), clock.GetUtcNow()); }
        catch (Exception) { return (null, null); }
    }

    private void Record(string scope, string executable, IReadOnlyList<string> arguments, string root,
        (long? Tick, DateTimeOffset? Utc) start, ProcessOutput? result, bool fullStatuses, bool process)
    {
        try
        {
            var end = Start();
            double? elapsed = start.Tick is long first && end.Tick is long last
                ? clock.GetElapsedTime(first, last).TotalMilliseconds : null;
            var argv = new[] { executable }.Concat(arguments).ToArray();
            var record = new
            {
                schema = "lean-native-phase-v1", scope, kind = process ? "process" : "owner-total",
                started_at_utc = start.Utc, finished_at_utc = end.Utc,
                elapsed_ms = elapsed, timing_status = elapsed is >= 0 ? "measured" : "error",
                cwd = root, executable, argc = argv.Length,
                // SHA-256 of the UTF-8 JSON argv array; long module selections are
                // retained in inspect.sh's command log, never dumped into CI again.
                argv = argv.Length <= 16 ? argv : null,
                argv_sha256 = Convert.ToHexStringLower(SHA256.HashData(JsonSerializer.SerializeToUtf8Bytes(argv))),
                exit_code = result?.ExitCode, execution_status = result is null ? "runner-error" : "exited",
                lake_version = Version,
                lake_jobs = CountJobs(result, Version, fullStatuses,
                    process && executable == lake && scope != "report-inspection"),
                lean_compiler_invocations = (int?)null,
            };
            Records.Append("LEAN_NATIVE_PHASE ").Append(JsonSerializer.Serialize(record)).Append('\n');
        }
        catch (Exception)
        {
            // Even broken measurement must be visible and cannot replace the
            // child's result or exception. No guessed durations or zero counts.
            Records.Append("LEAN_NATIVE_PHASE {\"schema\":\"lean-native-phase-v1\",\"measurement_status\":\"error\",\"elapsed_ms\":null,\"lake_jobs\":null,\"lean_compiler_invocations\":null}\n");
        }
    }

    // Lake 4.33.0 Lake/Build/{Run,Job/Basic}.lean: verbose + no-ansi reports
    // every monitored job, including the initial computation (index 0) which
    // is excluded from the final registered-job total. Actions can be merged
    // across jobs. Built/Replayed are job statuses, NOT compiler invocations.
    private static readonly Regex StatusRow = new(
        @"^[✔ℹ⚠✖] \[(\d+)/(\d+)\](?: \(Optional\))? (Ran|Reused|Replayed|Unpacked|Fetched|Built|Running|Reusing|Replaying|Unpacking|Fetching|Building) .+$",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
    private static readonly Regex Completed = new(@"^Build completed successfully \((\d+) jobs?\)\.$",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);

    internal static object CountJobs(ProcessOutput? result, string? version, bool fullStatuses, bool applicable = true)
    {
        var rows = new Dictionary<int, string>();
        int? total = null;
        var largestDenominator = 0;
        var malformed = false;
        if (applicable && version == SupportedVersion && result is not null)
        {
            foreach (var line in Encoding.UTF8.GetString(result.StandardOutput).Split('\n')
                .Concat(Encoding.UTF8.GetString(result.StandardError).Split('\n')))
            {
                var row = StatusRow.Match(line.TrimEnd('\r'));
                if (row.Success)
                {
                    if (!int.TryParse(row.Groups[1].Value, CultureInfo.InvariantCulture, out var index)
                        || !int.TryParse(row.Groups[2].Value, CultureInfo.InvariantCulture, out var denominator)
                        || index > denominator || !rows.TryAdd(index, row.Groups[3].Value)) malformed = true;
                    else largestDenominator = Math.Max(largestDenominator, denominator);
                }
                var summary = Completed.Match(line.TrimEnd('\r'));
                if (summary.Success)
                {
                    if (total is not null || !int.TryParse(summary.Groups[1].Value, CultureInfo.InvariantCulture, out var count))
                        malformed = true;
                    else total = count;
                }
            }
        }
        var complete = fullStatuses && !malformed && result?.ExitCode == 0 && total is >= 0
            && largestDenominator == total && rows.Count > 0 && rows.Count - 1 == total
            && rows.Keys.Min() == 0 && rows.Keys.Max() == total;
        var observed = rows.Count > 0 && !malformed;
        return new
        {
            status = !applicable ? "not-applicable" : complete ? "complete" : observed ? "partial" : "unknown",
            reason = !applicable ? "not-a-lake-build" : version != SupportedVersion ? "unsupported-or-missing-lake-version"
                : complete ? "all-monitored-statuses" : "missing-or-incomplete-status-coverage",
            built = complete ? rows.Values.Count(value => value == "Built") : (int?)null,
            replayed = complete ? rows.Values.Count(value => value == "Replayed") : (int?)null,
            observed_built = observed ? rows.Values.Count(value => value == "Built") : (int?)null,
            observed_replayed = observed ? rows.Values.Count(value => value == "Replayed") : (int?)null,
            registered_jobs = total, status_rows = observed ? rows.Count : (int?)null,
        };
    }
}
