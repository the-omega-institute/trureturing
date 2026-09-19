using System.Diagnostics;
using System.Runtime;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Xml.Linq;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal enum SeedExportMode { Automatic, Deferred }

internal sealed class CommonStages(string root, TextWriter output, CancellationToken deadlineCancellation = default,
    Action<Process>? processExited = null, TimeProvider? timeProvider = null, SeedExportMode seedExport = SeedExportMode.Automatic)
{
    private readonly List<StageStep> steps = [];
    private string stage = "input";
    private string? candidate;
    private int? testsExecuted;
    private int? testsReused;
    private bool? testSeedSaved;
    private ResourceExecutionPlan? resourcePlan;
    private CommonExecutionEvidence.CheckExecution? engineeringChecks;
    private string? attemptedEngineeringCheck;
    private readonly bool exportSeeds = seedExport == SeedExportMode.Automatic
        && Environment.GetEnvironmentVariable("STRATALINT_CACHE_WRITES") != "false";

    internal static int Normalize(int raw, bool allowProtectedAnnotation = false) => raw switch
    {
        0 => 0,
        1 => 1,
        3 when allowProtectedAnnotation => 0,
        _ => 2,
    };

    internal int Run(string name, string? baseSha, string? buildRound = null, string? planPath = null, string? changesPath = null)
    {
        stage = name;
        var exit = 2;
        string? failure = null;
        try
        {
            if (name is not ("build" or "engineering" or "current" or "delta")) throw new ArgumentException("invalid stage");
            if (name == "current") ClearEvidence("current");
            resourcePlan = ResourceExecutionPlan.Load(root, planPath, changesPath);
            if (name == "delta" && resourcePlan is not null
                && (resourcePlan.Document.GetProperty("mode").GetString() != "pr"
                    || resourcePlan.Document.GetProperty("base").GetString() != baseSha))
                throw new InvalidDataException("delta requires the validated plan's explicit immutable base");
            if (name == "delta") ValidateBase(baseSha);
            if (resourcePlan is not null && !resourcePlan.StageRequired(name))
            {
                candidate = resourcePlan.Commit;
                ClearEvidence(name);
                if (name == "current") File.Delete(Path.Combine(root, CommonExecutionEvidence.ScribeMarkdownPaths));
                exit = 0;
            }
            else
            {
                candidate = CommonExecutionEvidence.Candidate(root);
                switch (name)
                {
                    case "build": Build(); break;
                    case "engineering": Engineering(buildRound); break;
                    case "current": Current(); break;
                    case "delta": Delta(baseSha); break;
                    default: throw new ArgumentException("stage must be build, engineering, current, or delta");
                }
                // Engineering checks its final source snapshot immediately before sealing.
                if (name is not ("engineering" or "build") && candidate != CommonExecutionEvidence.Candidate(root))
                    throw new InvalidDataException("candidate changed during stage");
                exit = 0;
            }
        }
        catch (InvalidDataException exception) when (steps.LastOrDefault() is { Status: "failed" } failed)
        { exit = failed.Exit; failure = exception.Message; }
        catch (StageFailure exception) { exit = exception.Exit; failure = exception.Message; }
        catch (Exception exception) { failure = exception.Message; }
        finally { exit = Summarize(exit, failure, baseSha); }
        return exit;
    }

    private int Summarize(int exit, string? failure, string? baseSha)
    {
        var planned = stage switch
        {
            "build" => CommonExecutionEvidence.BuildSteps,
            "engineering" => [.. CommonExecutionEvidence.EngineeringSteps, .. engineeringChecks?.Ids ?? CommonExecutionEvidence.EngineeringCheckIds],
            "current" => CommonExecutionEvidence.CurrentSteps,
            "delta" => ["check-delta"],
            _ => [],
        };
        var required = resourcePlan is null || resourcePlan.StageRequired(stage);
        var obligations = !required ? [] : stage == "current" && resourcePlan is not null ? resourcePlan.CurrentSteps : planned;
        // Check units can be accepted from validated reuse without launching an
        // operation. A failed unit is attempted even when its validation fails
        // after zero-exit operations (for example, unequal selftest output).
        var checkUnits = stage == "engineering" ? (engineeringChecks?.Ids ?? CommonExecutionEvidence.EngineeringCheckIds).Select(id =>
        {
            var accepted = engineeringChecks?.Completed.SingleOrDefault(unit => unit.Id == id);
            return new { id, status = !required ? "not-required" : accepted?.Status
                    ?? (attemptedEngineeringCheck == id ? "failed" : "not-executed"),
                execution_candidate = accepted?.ExecutionCandidate, execution_round = accepted?.ExecutionRound };
        }).ToArray() : [];
        string? Artifact(string path) => required && File.Exists(Path.Combine(root, path)) ? path : null;
        object Summary() => new { stage, candidate, git_candidate = resourcePlan?.Document.GetProperty("candidate"),
            scope = resourcePlan?.Document, status = exit != 0 ? "failed" : required ? "completed" : "not-required",
            base_sha = baseSha, exit, error = failure, steps,
            artifacts = required ? new[] { CommonExecutionEvidence.BuildPath, CommonExecutionEvidence.TestsPath, CommonExecutionEvidence.EngineeringPath, CommonExecutionEvidence.CurrentPath }
                .Where(path => File.Exists(Path.Combine(root, path))).ToArray() : [],
            test_projects_executed = testsExecuted, test_projects_reused = testsReused, test_seed_saved = testSeedSaved,
            check_units = checkUnits,
            not_executed = obligations.Where(name => !steps.Any(step => step.Name == name)
                && !checkUnits.Any(unit => unit.id == name && unit.status != "not-executed")),
            not_required = planned.Except(obligations),
            build_evidence = Artifact(CommonExecutionEvidence.BuildPath), test_evidence = Artifact(CommonExecutionEvidence.TestsPath),
            engineering_evidence = Artifact(CommonExecutionEvidence.EngineeringPath),
            current_evidence = Artifact(CommonExecutionEvidence.CurrentPath), report = required && (resourcePlan?.CurrentSteps ?? CommonExecutionEvidence.CurrentSteps).Contains("lean-report") ? Artifact(CommonExecutionEvidence.ReportPath) : null };
        try { CommonExecutionEvidence.Write(root, CommonExecutionEvidence.RootPath + "/" + stage + "-result.json", Summary()); }
        catch (Exception exception) { exit = 2; failure = $"{failure}; summary write failed: {exception.Message}"; }
        output.WriteLine(JsonSerializer.Serialize(Summary()));
        return exit;
    }

    private void ClearEvidence(params string[] stages)
    {
        Directory.CreateDirectory(Path.Combine(root, CommonExecutionEvidence.RootPath));
        foreach (var name in stages)
            foreach (var suffix in new[] { ".json", "-checks.json", "-paths.nul", "-transport.json", "-result.json" })
                File.Delete(Path.Combine(root, CommonExecutionEvidence.RootPath, name + suffix));
    }

    private CommonStageRecord Build()
    {
        ClearEvidence("build", "engineering", "current");
        File.Delete(Path.Combine(root, CommonExecutionEvidence.TestsPath));
        var outputs = Path.Combine(root, CommonBuildOutputs.RootPath);
        if (Directory.Exists(outputs)) Directory.Delete(outputs, recursive: true);
        // Captured restore/build calls own their nodes until the output closes.
        var roots = BuildRoots();
        var logger = Environment.GetEnvironmentVariable("CI_CSC_LOGGER_ASSEMBLY");
        string[] observation = File.Exists(logger) ? ["-logger:StrataLint.JudgeSeed.CscExecutionLogger," + logger] : [];
        if (observation.Length == 0) output.WriteLine("JUDGE_CSC {\"status\":\"unavailable\",\"count\":null}");
        var projectSet = Path.Combine(root, CommonExecutionEvidence.RootPath, "selected-build.slnx");
        new XElement("Solution", roots.Select(target =>
            new XElement("Project", new XAttribute("Path", Path.Combine(root, target))))).Save(projectSet);
        // Keep references outside this explicit root list in the requested configuration.
        string[] buildOptions = ["-nr:false", "-m:1", "-p:ShouldUnsetParentConfigurationAndPlatform=false"];
        Step("restore-StrataLint", "dotnet", ["restore", projectSet, "--locked-mode", .. buildOptions]);
        Step("build", "dotnet", ["build", projectSet, "--configuration", "Release", "--no-restore", "--warnaserror", .. buildOptions,
            "-p:CustomAfterMicrosoftCommonTargets=" + Path.Combine(root, "tools/scripts/ci-build-outputs.targets"),
            "-p:CiRepositoryRoot=" + root, "-p:CiBuildOutputRoot=" + outputs, .. observation]);
        return CommonExecutionEvidence.SealBuild(root, candidate!, CommonBuildOutputs.Collect(root, roots), steps.ToArray(), roots, resourcePlan?.Retain(root));
    }

    private string[] BuildRoots()
    {
        var registry = EngineeringProjectRegistry.Read(CommonExecutionEvidence.Snapshot(root));
        var roots = resourcePlan?.Projects ?? registry.Projects.Where(project => project.Ci).Select(project => project.Path).Order(StringComparer.Ordinal).ToArray();
        if (roots.Length == 0) throw new InvalidDataException("no registered requested build roots");
        return roots;
    }

    private void Engineering(string? buildRound)
    {
        ClearEvidence("engineering");
        File.Delete(Path.Combine(root, CommonExecutionEvidence.TestsPath));
        CommonStageRecord build;
        if (buildRound is null)
        {
            stage = "build";
            build = Build();
            if (Summarize(0, null, null) != 0) throw new StageFailure(2, "build summary failed");
            steps.Clear();
            stage = "engineering";
        }
        else build = CommonExecutionEvidence.ValidateBuild(root, buildRound);
        var checks = engineeringChecks = CommonExecutionEvidence.BeginChecks(root, "engineering", build, output);
        try { Step("tests", "dotnet", [CommonExecutionEvidence.RunnerPath, "--repository", root, "--build-round", build.Round]); }
        finally
        {
            if (File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)))
            {
                var tests = CommonExecutionEvidence.Read<TestExecutionRecord>(root, CommonExecutionEvidence.TestsPath);
                testsExecuted = tests.Projects.Count(project => project.Status == "executed");
                testsReused = tests.Projects.Count(project => project.Status == "reused");
            }
        }
        attemptedEngineeringCheck = "selftest-pair";
        checks.Run(attemptedEngineeringCheck, () => new CheckWork([
            Operation("selftest-first", [CommonExecutionEvidence.CliPath, "selftest"]),
            Operation("selftest-second", [CommonExecutionEvidence.CliPath, "selftest"])]));
        foreach (var (id, project) in new[] {
            ("capability-proof", "tools/tests/CompileFailProof/CompileFailProof.csproj"),
            ("banned-api-proof", "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj") })
        {
            attemptedEngineeringCheck = id;
            checks.Run(id, () =>
            {
                var restore = Operation("restore-" + Path.GetFileNameWithoutExtension(project), ["restore", project, "--locked-mode", "-nr:false"]);
                if (restore.RawExit != 0) return new CheckWork([restore]);
                return new CheckWork([restore, Operation(id, ["build", project, "--no-restore", "--no-dependencies", "--configuration", "Release", "-nr:false"])]);
            });
        }
        _ = checks.Seal();
        CommonExecutionEvidence.SealEngineering(root, build, steps.Where(step => step.Name == "tests").ToArray());
        testSeedSaved = exportSeeds && CommonExecutionEvidence.ExportTestSeed(root, output);
        if (exportSeeds) _ = CommonExecutionEvidence.ExportCheckSeed(root, "engineering", output);
    }

    private CheckOperation Operation(string name, string[] arguments)
    {
        var result = Capture("dotnet", arguments);
        output.WriteLine(result.Text);
        var proof = name == "capability-proof" ? CompilationProof.ValidateCapability(result.Exit, result.Text)
            : name == "banned-api-proof" ? CompilationProof.ValidateBannedApi(result.Exit, result.Text,
                File.ReadAllText(Path.Combine(root, "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"))) : result.Exit == 0;
        var exit = proof ? 0 : result.Exit is 0 or 1 ? 1 : 2;
        var log = $"{CommonExecutionEvidence.RootPath}/logs/engineering/{name}.log";
        Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(root, log))!);
        File.WriteAllText(Path.Combine(root, log), result.Text);
        steps.Add(new(name, result.Exit, exit, exit == 0 ? "executed" : "failed", log));
        return new(name, result.Exit, result.Text);
    }

    private void Current()
    {
        ClearEvidence("current");
        File.Delete(Path.Combine(root, CommonExecutionEvidence.ScribeMarkdownPaths));
        var build = CommonExecutionEvidence.ValidateBuild(root);
        var obligations = resourcePlan?.CurrentSteps ?? CommonExecutionEvidence.CurrentSteps;
        var ids = resourcePlan?.CheckUnits.Except(CommonExecutionEvidence.EngineeringCheckIds).Order(StringComparer.Ordinal).ToArray()
            ?? CommonExecutionEvidence.CheckIds("current", CommonExecutionEvidence.ReadCheckManifest(CommonExecutionEvidence.Snapshot(root)));
        var runReport = obligations.Contains("lean-report");
        if (runReport) RequireBinary(build, CommonExecutionEvidence.LeanProducerPath);
        if (ids.Length != 0) RequireBinary(build, CommonExecutionEvidence.CliPath);
        var logs = Path.Combine(root, CommonExecutionEvidence.RootPath, "logs/current");
        if (Directory.Exists(logs)) Directory.Delete(logs, recursive: true);
        var reportBudget = TimeSpan.FromSeconds(LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds);
        string SupervisorBudget(string name) => Environment.GetEnvironmentVariable(name) is { Length: > 0 } value
            ? value : LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds.ToString(System.Globalization.CultureInfo.InvariantCulture);
        // Shared current supports normal cold production within the existing Lean
        // envelope. Nested defaults must not silently shorten that allowance.
        if (runReport)
        {
            Step("lean-report", "/usr/bin/env", [$"STRATALINT_LEAN_PRODUCER_DLL={Path.Combine(root, CommonExecutionEvidence.LeanProducerPath)}",
                $"STRATALINT_BUILD_TIMEOUT_SECONDS={SupervisorBudget("STRATALINT_BUILD_TIMEOUT_SECONDS")}",
                $"STRATALINT_LOCK_TIMEOUT_SECONDS={SupervisorBudget("STRATALINT_LOCK_TIMEOUT_SECONDS")}",
                $"STRATALINT_LEAN_REPORT_LOG_DIR={Path.Combine(logs, "lean-inspector")}",
                "make", "--no-print-directory", "lean-report"], defaultTimeout: reportBudget);
            ValidateCurrentReport();
        }
        else if (obligations.Contains("lean"))
            Step("lean", "make", ["--no-print-directory", "lean"]);
        if (ids.Length != 0)
        {
            if (ids.SequenceEqual(new[] { "filemap" }))
            {
                var checks = CommonExecutionEvidence.BeginChecks(root, "current", build, output, ids);
                checks.Run("filemap", () =>
                {
                    var result = Capture("dotnet", [CommonExecutionEvidence.CliPath, "filemap-conform"]);
                    return new([new("filemap", result.Exit, result.Text)]);
                });
                _ = checks.Seal();
            }
            else
            {
                var arguments = new List<string> { CommonExecutionEvidence.CliPath, "check-current" };
                if (runReport) arguments.AddRange(["--candidate-lean-report", CommonExecutionEvidence.ReportPath]);
                arguments.AddRange(["--common-build-round", build.Round]);
                if (resourcePlan is not null)
                    arguments.AddRange(["--common-plan", resourcePlan.PlanPath, "--common-changes", resourcePlan.ChangesPath]);
                // The CLI builds its own snapshot and report. Reclaim the dead
                // parent preparation graphs only at this separate-process handoff.
                GCSettings.LargeObjectHeapCompactionMode = GCLargeObjectHeapCompactionMode.CompactOnce;
                ObserveCurrentMemory("before-collection", build);
                GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true, compacting: true);
                ObserveCurrentMemory("after-collection", build);
                Step(obligations.Contains("check-current") ? "check-current" : "scribe", "dotnet", arguments.ToArray());
                // The CLI owned these units once; their original evidence supplies the
                // corresponding stage obligations without launching them a second time.
                steps.RemoveAt(steps.Count - 1);
            }
        }
        output.WriteLine("CURRENT_FINALIZE phase=seal status=started");
        var completed = CommonExecutionEvidence.CompleteCurrent(root, build, steps.ToArray(), resourcePlan);
        steps.Clear();
        steps.AddRange(completed);
        output.WriteLine("CURRENT_FINALIZE phase=seal status=completed");
        if (ids.Length != 0 && exportSeeds)
        {
            output.WriteLine("CURRENT_FINALIZE phase=seed-export status=started");
            _ = CommonExecutionEvidence.ExportCheckSeed(root, "current", output);
            output.WriteLine("CURRENT_FINALIZE phase=seed-export status=completed");
        }
    }

    // End the validation frame before collection; no snapshot or report escapes.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private void ValidateCurrentReport() =>
        _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, CommonExecutionEvidence.ReportPath), CommonExecutionEvidence.Snapshot(root), validateMaterials: true);

    // Observations are not acceptance evidence. Keep readers and output failures
    // outside the validation/child exit contract; never print exception messages.
    private void ObserveCurrentMemory(string boundary, CommonStageRecord build) =>
        WriteCurrentDiagnostic("CURRENT_HANDOFF_MEMORY", () => new
        {
            boundary, unix_time_ms = (timeProvider ?? TimeProvider.System).GetUtcNow().ToUnixTimeMilliseconds(),
            parent_pid = Environment.ProcessId, candidate, build_round = build.Round,
            plan_present = resourcePlan is not null,
            assembly_sha256 = ObserveMemoryValue(() =>
            {
                using var assembly = File.OpenRead(typeof(CommonStages).Assembly.Location);
                return Convert.ToHexStringLower(SHA256.HashData(assembly));
            }),
            runtime_version = Environment.Version.ToString(), framework = RuntimeInformation.FrameworkDescription,
            process_architecture = RuntimeInformation.ProcessArchitecture.ToString(),
            server_gc = GCSettings.IsServerGC, latency_mode = GCSettings.LatencyMode.ToString(),
            managed_bytes = GC.GetTotalMemory(false),
            gc = ObserveMemoryValue(() =>
            {
                var info = GC.GetGCMemoryInfo();
                return new
                {
                    heap_size_bytes = info.HeapSizeBytes, fragmented_bytes = info.FragmentedBytes,
                    total_committed_bytes = info.TotalCommittedBytes, index = info.Index,
                    generation = info.Generation, compacted = info.Compacted,
                    pause_ms = info.PauseDurations.ToArray().Select(pause => pause.TotalMilliseconds).ToArray(),
                    pause_time_percentage = info.PauseTimePercentage,
                    collection_counts = Enumerable.Range(0, GC.MaxGeneration + 1).Select(GC.CollectionCount).ToArray(),
                };
            }),
            rss_bytes = ObserveMemoryValue(() =>
            {
                using var process = Process.GetCurrentProcess();
                return process.WorkingSet64;
            }),
            smaps_rollup_bytes = ReadMemoryCounters(() => LinuxLines("/proc/self/smaps_rollup"),
                ["Rss", "Anonymous", "Private_Dirty", "LazyFree", "Swap"], kibibytes: true),
            cgroup_memory_stat_bytes = ReadMemoryCounters(() =>
                File.ReadLines(ResolveMemoryStat(LinuxLines("/proc/self/cgroup"), LinuxLines("/proc/self/mountinfo"))),
                ["anon", "file", "kernel"], kibibytes: false),
        });

    internal void WriteCurrentDiagnostic(string name, Func<object> observation)
    {
        try
        {
            output.WriteLine(name + " " + JsonSerializer.Serialize(observation()));
            output.Flush();
        }
        catch (Exception) { } // Best-effort diagnostics must not affect stage behavior.
    }

    private static object UnavailableMemory(string reason) => new { unavailable = reason };

    private static object ObserveMemoryValue<T>(Func<T> read)
    {
        try { return read()!; }
        catch (Exception exception) { return UnavailableMemory(exception.GetType().Name); }
    }

    private static IEnumerable<string> LinuxLines(string path)
    {
        if (!OperatingSystem.IsLinux()) throw new PlatformNotSupportedException();
        return File.ReadLines(path);
    }

    internal static Dictionary<string, object> ReadMemoryCounters(Func<IEnumerable<string>> read, string[] fields, bool kibibytes)
    {
        var values = fields.ToDictionary(field => field, _ => UnavailableMemory("missing-field"), StringComparer.Ordinal);
        try
        {
            foreach (var line in read())
            {
                var words = line.Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries);
                if (words.Length == 0 || !values.ContainsKey(words[0].TrimEnd(':'))) continue;
                var field = words[0].TrimEnd(':');
                values[field] = words.Length == (kibibytes ? 3 : 2) && (!kibibytes || words[2] == "kB")
                    && long.TryParse(words[1], System.Globalization.NumberStyles.None,
                        System.Globalization.CultureInfo.InvariantCulture, out var value) && value >= 0
                    && value <= long.MaxValue / (kibibytes ? 1024 : 1)
                    ? value * (kibibytes ? 1024 : 1) : UnavailableMemory("invalid-value");
            }
        }
        catch (Exception exception)
        {
            // A partial read is not a complete observation, including on access denial.
            foreach (var field in fields) values[field] = UnavailableMemory(exception.GetType().Name);
        }
        return values;
    }

    internal static string ResolveMemoryStat(IEnumerable<string> memberships, IEnumerable<string> mounts)
    {
        var groups = memberships.Select(line => line.Split(':', 3)).Where(parts => parts.Length == 3).ToArray();
        foreach (var line in mounts)
        {
            var halves = line.Split(" - ", 2, StringSplitOptions.None);
            if (halves.Length != 2) continue;
            var mount = halves[0].Split(' ');
            var filesystem = halves[1].Split(' ');
            if (mount.Length < 6 || filesystem.Length < 3) continue;
            var group = filesystem[0] == "cgroup2" ? groups.FirstOrDefault(parts => parts[0] == "0" && parts[1] == "")
                : filesystem[0] == "cgroup" && filesystem[2].Split(',').Contains("memory")
                    ? groups.FirstOrDefault(parts => parts[1].Split(',').Contains("memory")) : null;
            if (group is null) continue;
            var mountRoot = UnescapeMount(mount[3]);
            var mountPoint = UnescapeMount(mount[4]);
            var groupPath = group[2];
            if (!mountRoot.StartsWith('/') || !mountPoint.StartsWith('/') || !groupPath.StartsWith('/')
                || groupPath.Split('/').Any(part => part is "." or "..")) continue;
            var relative = mountRoot == "/" ? groupPath.TrimStart('/')
                : groupPath == mountRoot ? ""
                : groupPath.StartsWith(mountRoot + "/", StringComparison.Ordinal) ? groupPath[(mountRoot.Length + 1)..] : null;
            if (relative is not null) return Path.Combine(mountPoint, relative, "memory.stat");
        }
        throw new NotSupportedException("memory cgroup mount unavailable");
    }

    private static string UnescapeMount(string value) => value.Replace("\\040", " ", StringComparison.Ordinal)
        .Replace("\\011", "\t", StringComparison.Ordinal).Replace("\\012", "\n", StringComparison.Ordinal)
        .Replace("\\134", "\\", StringComparison.Ordinal);

    private void ValidateBase(string? baseSha)
    {
        if (baseSha is null || baseSha.Length != 40 || !baseSha.All(char.IsAsciiHexDigit))
            throw new ArgumentException("delta requires an explicit 40-hex base commit SHA");
        var type = Capture("git", ["cat-file", "-t", baseSha]);
        if (type.Exit != 0 || type.Text.Trim() != "commit") throw new ArgumentException("base must be an available commit object");
    }

    private void Delta(string? baseSha)
    {
        var build = CommonExecutionEvidence.ValidateBuild(root);
        RequireBinary(build, CommonExecutionEvidence.CliPath);
        Step("check-delta", "dotnet", [CommonExecutionEvidence.CliPath, "check-delta", "--protected-base", baseSha!,
            "--candidate-lean-report", CommonExecutionEvidence.ReportPath], allowAnnotation: true);
    }

    private static void RequireBinary(CommonStageRecord record, string path)
    {
        if (!record.Materials.Any(material => material.Path == path)) throw new InvalidDataException("unbound candidate binary: " + path);
    }

    private string Step(string name, string executable, string[] arguments, Func<int, string, bool>? proof = null,
        bool allowAnnotation = false, TimeSpan? defaultTimeout = null)
    {
        output.WriteLine("STAGE_STEP " + JsonSerializer.Serialize(new { stage, name, status = "started" }));
        output.Flush();
        var result = Capture(executable, arguments, defaultTimeout, streamOutput: true);
        var log = $"{CommonExecutionEvidence.RootPath}/logs/{stage}/{name}{(steps.Any(step => step.Name == name) ? "-" + steps.Count : "")}.log";
        var full = Path.Combine(root, log);
        Directory.CreateDirectory(Path.GetDirectoryName(full)!);
        File.WriteAllText(full, result.Text);
        var exit = proof is null ? Normalize(result.Exit, allowAnnotation)
            : result.Exit is not (0 or 1) ? 2 : proof(result.Exit, result.Text) ? 0 : 1;
        steps.Add(new(name, result.Exit, exit, exit == 0 ? "executed" : "failed", log));
        if (exit != 0) throw new StageFailure(exit, $"{name} failed: raw_exit={result.Exit}; log={log}");
        return result.Text;
    }

    private (int Exit, string Text) Capture(string executable, string[] arguments, TimeSpan? defaultTimeout = null,
        bool streamOutput = false)
    {
        var clock = timeProvider ?? TimeProvider.System;
        if (deadlineCancellation.IsCancellationRequested) throw new TimeoutException("PREFLIGHT_BUDGET_EXHAUSTED owner=outer-deadline");
        // Injected deadlines are advanced by their owner, independent of the ambient clock.
        var timeout = deadlineCancellation.CanBeCanceled ? Timeout.InfiniteTimeSpan : defaultTimeout ?? TimeSpan.FromHours(2);
        var deadline = deadlineCancellation.CanBeCanceled ? null : Environment.GetEnvironmentVariable("PREFLIGHT_DEADLINE_AT");
        if (deadline is not null)
        {
            if (!long.TryParse(deadline, System.Globalization.NumberStyles.Integer,
                    System.Globalization.CultureInfo.InvariantCulture, out var seconds))
                throw new ArgumentException("invalid PREFLIGHT_DEADLINE_AT");
            timeout = DateTimeOffset.FromUnixTimeSeconds(seconds) - clock.GetUtcNow();
            if (timeout <= TimeSpan.Zero) throw new TimeoutException("PREFLIGHT_BUDGET_EXHAUSTED owner=outer-deadline");
        }
        var start = new ProcessStartInfo(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
        start.Environment["DOTNET_CLI_UI_LANGUAGE"] = "en-US";
        start.Environment["CI"] = "true";
        if (stage == "current")
        {
            // A missing optional seed must reach the selected producer. The local
            // ensure command retains its guard outside CI/preflight's child scope.
            start.Environment["STRATALINT_ACCEPT_COLD_BUILD"] = "1";
        }
        if (stage != "build" && Directory.Exists(Path.Combine(root, CommonBuildOutputs.PackagesPath)))
            start.Environment["NUGET_PACKAGES"] = Path.Combine(root, CommonBuildOutputs.PackagesPath);
        foreach (var arg in arguments) start.ArgumentList.Add(arg);
        var startedAt = clock.GetTimestamp();
        double Elapsed() => clock.GetElapsedTime(startedAt).TotalMilliseconds;
        using var process = Process.Start(start) ?? throw new IOException("cannot start " + executable);
        if (stage == "current" && arguments.Length >= 2 && arguments[0] == CommonExecutionEvidence.CliPath && arguments[1] == "check-current")
            WriteCurrentDiagnostic("CURRENT_HANDOFF_CHILD", () => new
            {
                unix_time_ms = clock.GetUtcNow().ToUnixTimeMilliseconds(), parent_pid = Environment.ProcessId,
                child_pid = process.Id, candidate,
                build_round = arguments.SkipWhile(argument => argument != "--common-build-round").Skip(1).FirstOrDefault(),
                plan_present = resourcePlan is not null,
            });
        var startedElapsed = Elapsed();
        using var timer = new CancellationTokenSource(timeout, clock);
        using var cancellation = CancellationTokenSource.CreateLinkedTokenSource(deadlineCancellation, timer.Token);
        using var drainCancellation = new CancellationTokenSource();
        using var stdoutReader = process.StandardOutput;
        using var stderrReader = process.StandardError;
        var stdoutText = new StringBuilder();
        var stderrText = new StringBuilder();
        var liveOutput = streamOutput ? TextWriter.Synchronized(output) : null;
        var phase = "child-exit";
        var outcome = "faulted";
        string? cancelledPhase = null;
        double? cancelledElapsed = null;
        var deadlineCancelled = false;
        var timeoutCancelled = false;
        var childExit = new { code = (int?)null, phase = "not-observed", elapsed_ms = (double?)null };
        var stdoutObservation = new { status = "pending", elapsed_ms = (double?)null };
        var stderrObservation = stdoutObservation;
        async Task WaitForExit(CancellationToken token)
        {
            var waitPhase = phase;
            await process.WaitForExitAsync(token).ConfigureAwait(false);
            if (childExit.code is null)
                childExit = new { code = (int?)process.ExitCode, phase = waitPhase, elapsed_ms = (double?)Elapsed() };
        }
        var stdout = Drain(stdoutReader, stdoutText, liveOutput, drainCancellation.Token,
            status => stdoutObservation = new { status, elapsed_ms = (double?)Elapsed() });
        var stderr = Drain(stderrReader, stderrText, liveOutput, drainCancellation.Token,
            status => stderrObservation = new { status, elapsed_ms = (double?)Elapsed() });
        var drains = Task.WhenAll(stdout, stderr);
        try
        {
            WaitForExit(cancellation.Token).GetAwaiter().GetResult();
            phase = "output-drain";
            processExited?.Invoke(process);
            drains.WaitAsync(cancellation.Token).GetAwaiter().GetResult();
            cancellation.Token.ThrowIfCancellationRequested();
            outcome = "completed";
            return (process.ExitCode, Captured(stdoutText) + Captured(stderrText));
        }
        catch (OperationCanceledException)
        {
            cancelledPhase = phase;
            cancelledElapsed = Elapsed();
            deadlineCancelled = deadlineCancellation.IsCancellationRequested;
            timeoutCancelled = timer.IsCancellationRequested;
            outcome = "cancelled";
            phase = "cleanup";
            // Keep reading bytes emitted before the deadline while killing/reaping
            // the producer. An inherited pipe can stay open after its parent exits,
            // so the readers share the existing five-second cleanup bound.
            drainCancellation.CancelAfter(TimeSpan.FromSeconds(5));
            try { if (!process.HasExited) process.Kill(entireProcessTree: true); }
            catch (InvalidOperationException) { } // Exit can race the kill.
            try
            {
                Task.WhenAll(drains, WaitForExit(drainCancellation.Token)).GetAwaiter().GetResult();
            }
            catch (OperationCanceledException) { }
            var diagnostic = "\nstage deadline exceeded: " + executable + "\n";
            liveOutput?.Write(diagnostic);
            liveOutput?.Flush();
            return (124, Captured(stdoutText) + Captured(stderrText) + diagnostic);
        }
        finally
        {
            // Join the actual collectors, including on exceptional exits; a timed
            // wait alone could return with a collector still owning a pipe/buffer.
            drainCancellation.Cancel();
            try { drains.GetAwaiter().GetResult(); }
            catch (OperationCanceledException) { }
            finally
            {
                // A child may finish without a newline. Keep the observation on
                // its own line without changing the retained predicate text.
                liveOutput?.WriteLine();
                output.WriteLine("STAGE_PROCESS " + JsonSerializer.Serialize(new
                {
                    stage, command = executable, arguments, process_id = process.Id, phase, outcome,
                    started_elapsed_ms = startedElapsed, elapsed_ms = Elapsed(),
                    timeout_ms = timeout == Timeout.InfiniteTimeSpan ? (double?)null : timeout.TotalMilliseconds,
                    cancelled_phase = cancelledPhase, cancelled_elapsed_ms = cancelledElapsed,
                    deadline_cancelled = deadlineCancelled, timeout_cancelled = timeoutCancelled,
                    child_exit = childExit, stdout = stdoutObservation, stderr = stderrObservation,
                }));
                output.Flush();
            }
        }
    }

    private static async Task Drain(StreamReader reader, StringBuilder text, TextWriter? output,
        CancellationToken cancellation, Action<string> observed)
    {
        var status = "faulted";
        try
        {
            var buffer = new char[4096];
            int count;
            while ((count = await reader.ReadAsync(buffer.AsMemory(), cancellation).ConfigureAwait(false)) != 0)
            {
                lock (text) text.Append(buffer, 0, count);
                if (output is not null)
                {
                    lock (output)
                    {
                        output.Write(buffer, 0, count);
                        output.Flush();
                    }
                }
            }
            status = "eof";
        }
        catch (OperationCanceledException) { status = "cancelled"; throw; }
        finally { observed(status); }
    }

    private static string Captured(StringBuilder text)
    {
        lock (text) return text.ToString();
    }

    private sealed class StageFailure(int exit, string message) : Exception(message)
    {
        internal int Exit { get; } = exit;
    }
}
