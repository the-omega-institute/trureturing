using System.Diagnostics;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed class CommonStages(string root, TextWriter output, CancellationToken deadlineCancellation = default,
    Action<Process>? processExited = null, TimeProvider? timeProvider = null)
{
    private readonly List<StageStep> steps = [];
    private string stage = "input";
    private string? candidate;
    private int? testsExecuted;
    private int? testsReused;
    private bool? testSeedSaved;

    internal static int Normalize(int raw, bool allowProtectedAnnotation = false) => raw switch
    {
        0 => 0,
        1 => 1,
        3 when allowProtectedAnnotation => 0,
        _ => 2,
    };

    internal int Run(string name, string? baseSha, string? buildRound = null)
    {
        stage = name;
        var exit = 2;
        string? failure = null;
        try
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
            "engineering" => CommonExecutionEvidence.EngineeringSteps,
            "current" => CommonExecutionEvidence.CurrentSteps,
            "delta" => ["check-delta"],
            _ => [],
        };
        object Summary() => new { stage, candidate, base_sha = baseSha, exit, error = failure, steps,
            test_projects_executed = testsExecuted, test_projects_reused = testsReused, test_seed_saved = testSeedSaved,
            not_executed = planned.Where(name => !steps.Any(step => step.Name == name)),
            build_evidence = CommonExecutionEvidence.BuildPath, test_evidence = CommonExecutionEvidence.TestsPath,
            engineering_evidence = CommonExecutionEvidence.EngineeringPath,
            current_evidence = CommonExecutionEvidence.CurrentPath, report = CommonExecutionEvidence.ReportPath };
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
        Step("restore-StrataLint", "dotnet", ["restore", "tools/StrataLint.sln", "--locked-mode", "-nr:false"]);
        Step("build", "dotnet", ["build", "tools/StrataLint.sln", "--configuration", "Release", "--no-restore", "--warnaserror", "-nr:false",
            "-p:CustomAfterMicrosoftCommonTargets=" + Path.Combine(root, "tools/scripts/ci-build-outputs.targets"),
            "-p:CiRepositoryRoot=" + root, "-p:CiBuildOutputRoot=" + outputs]);
        return CommonExecutionEvidence.SealBuild(root, candidate!, CommonBuildOutputs.Collect(root), steps.ToArray());
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
        var checks = CommonExecutionEvidence.BeginChecks(root, "engineering", build, output);
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
        checks.Run("selftest-pair", () => new CheckWork([
            Operation("selftest-first", [CommonExecutionEvidence.CliPath, "selftest"]),
            Operation("selftest-second", [CommonExecutionEvidence.CliPath, "selftest"])]));
        foreach (var (id, project) in new[] {
            ("capability-proof", "tools/tests/CompileFailProof/CompileFailProof.csproj"),
            ("banned-api-proof", "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj") })
            checks.Run(id, () =>
            {
                var restore = Operation("restore-" + Path.GetFileNameWithoutExtension(project), ["restore", project, "--locked-mode", "-nr:false"]);
                if (restore.RawExit != 0) return new CheckWork([restore]);
                return new CheckWork([restore, Operation(id, ["build", project, "--no-restore", "--no-dependencies", "--configuration", "Release", "-nr:false"])]);
            });
        _ = checks.Seal();
        CommonExecutionEvidence.SealEngineering(root, build, steps.Where(step => step.Name == "tests").ToArray());
        testSeedSaved = CommonExecutionEvidence.ExportTestSeed(root, output);
        _ = CommonExecutionEvidence.ExportCheckSeed(root, "engineering", output);
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
        _ = CommonExecutionEvidence.ReadCheckManifest(CommonExecutionEvidence.Snapshot(root));
        var build = CommonExecutionEvidence.ValidateBuild(root);
        RequireBinary(build, CommonExecutionEvidence.CliPath);
        RequireBinary(build, CommonExecutionEvidence.ScribePath);
        RequireBinary(build, CommonExecutionEvidence.RunnerPath);
        RequireBinary(build, CommonExecutionEvidence.LeanProducerPath);
        var logs = Path.Combine(root, CommonExecutionEvidence.RootPath, "logs/current");
        if (Directory.Exists(logs)) Directory.Delete(logs, recursive: true);
        var reportBudget = TimeSpan.FromSeconds(LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds);
        string SupervisorBudget(string name) => Environment.GetEnvironmentVariable(name) is { Length: > 0 } value
            ? value : LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds.ToString(System.Globalization.CultureInfo.InvariantCulture);
        // Shared current supports normal cold production within the existing Lean
        // envelope. Nested defaults must not silently shorten that allowance.
        Step("lean-report", "/usr/bin/env", [$"STRATALINT_LEAN_PRODUCER_DLL={Path.Combine(root, CommonExecutionEvidence.LeanProducerPath)}",
            $"STRATALINT_BUILD_TIMEOUT_SECONDS={SupervisorBudget("STRATALINT_BUILD_TIMEOUT_SECONDS")}",
            $"STRATALINT_LOCK_TIMEOUT_SECONDS={SupervisorBudget("STRATALINT_LOCK_TIMEOUT_SECONDS")}",
            $"STRATALINT_LEAN_REPORT_LOG_DIR={Path.Combine(logs, "lean-inspector")}",
            "make", "--no-print-directory", "lean-report"], defaultTimeout: reportBudget);
        _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, CommonExecutionEvidence.ReportPath), CommonExecutionEvidence.Snapshot(root), validateMaterials: true);
        Step("check-current", "dotnet", [CommonExecutionEvidence.CliPath, "check-current",
            "--candidate-lean-report", CommonExecutionEvidence.ReportPath, "--common-build-round", build.Round]);
        CommonExecutionEvidence.SealCurrent(root, build, steps.ToArray());
        _ = CommonExecutionEvidence.ExportCheckSeed(root, "current", output);
    }

    private void Delta(string? baseSha)
    {
        if (baseSha is null || baseSha.Length != 40 || !baseSha.All(char.IsAsciiHexDigit))
            throw new ArgumentException("delta requires an explicit 40-hex base commit SHA");
        var type = Capture("git", ["cat-file", "-t", baseSha]);
        if (type.Exit != 0 || type.Text.Trim() != "commit") throw new ArgumentException("base must be an available commit object");
        var common = CommonExecutionEvidence.ValidateCommon(root);
        RequireBinary(common.Build, CommonExecutionEvidence.CliPath);
        Step("check-delta", "dotnet", [CommonExecutionEvidence.CliPath, "check-delta", "--protected-base", baseSha,
            "--candidate-lean-report", CommonExecutionEvidence.ReportPath], allowAnnotation: true);
    }

    private static void RequireBinary(CommonStageRecord record, string path)
    {
        if (!record.Materials.Any(material => material.Path == path)) throw new InvalidDataException("unbound candidate binary: " + path);
    }

    private string Step(string name, string executable, string[] arguments, Func<int, string, bool>? proof = null,
        bool allowAnnotation = false, TimeSpan? defaultTimeout = null)
    {
        var result = Capture(executable, arguments, defaultTimeout);
        var log = $"{CommonExecutionEvidence.RootPath}/logs/{stage}/{name}.log";
        var full = Path.Combine(root, log);
        Directory.CreateDirectory(Path.GetDirectoryName(full)!);
        File.WriteAllText(full, result.Text);
        var exit = proof is null ? Normalize(result.Exit, allowAnnotation)
            : result.Exit is not (0 or 1) ? 2 : proof(result.Exit, result.Text) ? 0 : 1;
        steps.Add(new(name, result.Exit, exit, exit == 0 ? "executed" : "failed", log));
        output.WriteLine(result.Text);
        if (exit != 0) throw new StageFailure(exit, $"{name} failed: raw_exit={result.Exit}; log={log}");
        return result.Text;
    }

    private (int Exit, string Text) Capture(string executable, string[] arguments, TimeSpan? defaultTimeout = null)
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
        if (stage != "build" && Directory.Exists(Path.Combine(root, CommonBuildOutputs.PackagesPath)))
            start.Environment["NUGET_PACKAGES"] = Path.Combine(root, CommonBuildOutputs.PackagesPath);
        foreach (var arg in arguments) start.ArgumentList.Add(arg);
        var startedAt = clock.GetTimestamp();
        double Elapsed() => clock.GetElapsedTime(startedAt).TotalMilliseconds;
        using var process = Process.Start(start) ?? throw new IOException("cannot start " + executable);
        var startedElapsed = Elapsed();
        using var timer = new CancellationTokenSource(timeout, clock);
        using var cancellation = CancellationTokenSource.CreateLinkedTokenSource(deadlineCancellation, timer.Token);
        using var drainCancellation = new CancellationTokenSource();
        using var stdoutReader = process.StandardOutput;
        using var stderrReader = process.StandardError;
        var stdoutText = new StringBuilder();
        var stderrText = new StringBuilder();
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
        var stdout = Drain(stdoutReader, stdoutText, drainCancellation.Token,
            status => stdoutObservation = new { status, elapsed_ms = (double?)Elapsed() });
        var stderr = Drain(stderrReader, stderrText, drainCancellation.Token,
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
            return (124, Captured(stdoutText) + Captured(stderrText)
                + "\nstage deadline exceeded: " + executable + "\n");
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
                output.WriteLine("STAGE_PROCESS " + JsonSerializer.Serialize(new
                {
                    stage, command = executable, arguments, process_id = process.Id, phase, outcome,
                    started_elapsed_ms = startedElapsed, elapsed_ms = Elapsed(),
                    timeout_ms = timeout == Timeout.InfiniteTimeSpan ? (double?)null : timeout.TotalMilliseconds,
                    cancelled_phase = cancelledPhase, cancelled_elapsed_ms = cancelledElapsed,
                    deadline_cancelled = deadlineCancelled, timeout_cancelled = timeoutCancelled,
                    child_exit = childExit, stdout = stdoutObservation, stderr = stderrObservation,
                }));
            }
        }
    }

    private static async Task Drain(StreamReader reader, StringBuilder text, CancellationToken cancellation, Action<string> observed)
    {
        var status = "faulted";
        try
        {
            var buffer = new char[4096];
            int count;
            while ((count = await reader.ReadAsync(buffer.AsMemory(), cancellation).ConfigureAwait(false)) != 0)
            {
                lock (text) text.Append(buffer, 0, count);
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
