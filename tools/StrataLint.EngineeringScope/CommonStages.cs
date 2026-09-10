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
            foreach (var suffix in new[] { ".json", "-paths.nul", "-transport.json", "-result.json" })
                File.Delete(Path.Combine(root, CommonExecutionEvidence.RootPath, name + suffix));
    }

    private CommonStageRecord Build()
    {
        ClearEvidence("build", "engineering", "current");
        File.Delete(Path.Combine(root, CommonExecutionEvidence.TestsPath));
        var outputs = Path.Combine(root, CommonBuildOutputs.RootPath);
        if (Directory.Exists(outputs)) Directory.Delete(outputs, recursive: true);
        Step("restore-StrataLint", "dotnet", ["restore", "tools/StrataLint.sln", "--locked-mode"]);
        Step("build", "dotnet", ["build", "tools/StrataLint.sln", "--configuration", "Release", "--no-restore", "--warnaserror",
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
        foreach (var project in new[] { "tools/tests/CompileFailProof/CompileFailProof.csproj", "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj" })
            Step("restore-" + Path.GetFileNameWithoutExtension(project), "dotnet", ["restore", project, "--locked-mode"]);
        Step("tests", "dotnet", [CommonExecutionEvidence.RunnerPath, "--repository", root, "--all", "--build-round", build.Round]);
        var first = Step("selftest-first", "dotnet", [CommonExecutionEvidence.CliPath, "selftest"]);
        var second = Step("selftest-second", "dotnet", [CommonExecutionEvidence.CliPath, "selftest"]);
        if (first != second) throw new StageFailure(1, "selftest outputs differ");
        Step("capability-proof", "dotnet", ["build", "tools/tests/CompileFailProof/CompileFailProof.csproj", "--no-restore", "--no-dependencies", "--configuration", "Release"], CompilationProof.ValidateCapability);
        Step("banned-api-proof", "dotnet", ["build", "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", "--no-restore", "--no-dependencies", "--configuration", "Release"],
            (raw, text) => CompilationProof.ValidateBannedApi(raw, text, File.ReadAllText(Path.Combine(root, "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"))));
        CommonExecutionEvidence.SealEngineering(root, build, steps.ToArray());
    }

    private void Current()
    {
        ClearEvidence("current");
        var build = CommonExecutionEvidence.ValidateBuild(root);
        RequireBinary(build, CommonExecutionEvidence.CliPath);
        RequireBinary(build, CommonExecutionEvidence.ScribePath);
        RequireBinary(build, CommonExecutionEvidence.RunnerPath);
        var logs = Path.Combine(root, CommonExecutionEvidence.RootPath, "logs/current");
        if (Directory.Exists(logs)) Directory.Delete(logs, recursive: true);
        var reportBudget = TimeSpan.FromSeconds(LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds);
        string SupervisorBudget(string name) => Environment.GetEnvironmentVariable(name) is { Length: > 0 } value
            ? value : LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds.ToString(System.Globalization.CultureInfo.InvariantCulture);
        // Shared current supports normal cold production within the existing Lean
        // envelope. Nested defaults must not silently shorten that allowance.
        Step("lean-report", "/usr/bin/env", [$"STRATALINT_LEAN_PRODUCER_DLL={Path.Combine(root, CommonExecutionEvidence.RunnerPath)}",
            $"STRATALINT_BUILD_TIMEOUT_SECONDS={SupervisorBudget("STRATALINT_BUILD_TIMEOUT_SECONDS")}",
            $"STRATALINT_LOCK_TIMEOUT_SECONDS={SupervisorBudget("STRATALINT_LOCK_TIMEOUT_SECONDS")}",
            $"STRATALINT_LEAN_REPORT_LOG_DIR={Path.Combine(logs, "lean-inspector")}",
            "make", "--no-print-directory", "lean-report"], defaultTimeout: reportBudget);
        _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, CommonExecutionEvidence.ReportPath), CommonExecutionEvidence.Snapshot(root), validateMaterials: true);
        Step("scribe", "/bin/bash", ["tools/scripts/workflow/scribe-content-checks.sh", CommonExecutionEvidence.ReportPath, CommonExecutionEvidence.ScribePath]);
        Step("filemap", "dotnet", [CommonExecutionEvidence.CliPath, "filemap-conform"]);
        Step("check-current", "dotnet", [CommonExecutionEvidence.CliPath, "check-current", "--candidate-lean-report", CommonExecutionEvidence.ReportPath]);
        CommonExecutionEvidence.SealCurrent(root, build, steps.ToArray());
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
        if (stage != "build" && Directory.Exists(Path.Combine(root, CommonBuildOutputs.PackagesPath)))
            start.Environment["NUGET_PACKAGES"] = Path.Combine(root, CommonBuildOutputs.PackagesPath);
        foreach (var arg in arguments) start.ArgumentList.Add(arg);
        using var process = Process.Start(start) ?? throw new IOException("cannot start " + executable);
        using var timer = new CancellationTokenSource(timeout, clock);
        using var cancellation = CancellationTokenSource.CreateLinkedTokenSource(deadlineCancellation, timer.Token);
        using var drainCancellation = new CancellationTokenSource();
        using var stdoutReader = process.StandardOutput;
        using var stderrReader = process.StandardError;
        var stdoutText = new StringBuilder();
        var stderrText = new StringBuilder();
        var stdout = Drain(stdoutReader, stdoutText, drainCancellation.Token);
        var stderr = Drain(stderrReader, stderrText, drainCancellation.Token);
        var drains = Task.WhenAll(stdout, stderr);
        try
        {
            process.WaitForExitAsync(cancellation.Token).GetAwaiter().GetResult();
            processExited?.Invoke(process);
            drains.WaitAsync(cancellation.Token).GetAwaiter().GetResult();
            cancellation.Token.ThrowIfCancellationRequested();
            return (process.ExitCode, Captured(stdoutText) + Captured(stderrText));
        }
        catch (OperationCanceledException)
        {
            // Keep reading bytes emitted before the deadline while killing/reaping
            // the producer. An inherited pipe can stay open after its parent exits,
            // so the readers share the existing five-second cleanup bound.
            drainCancellation.CancelAfter(TimeSpan.FromSeconds(5));
            try { if (!process.HasExited) process.Kill(entireProcessTree: true); }
            catch (InvalidOperationException) { } // Exit can race the kill.
            try
            {
                Task.WhenAll(drains, process.WaitForExitAsync(drainCancellation.Token)).GetAwaiter().GetResult();
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
        }
    }

    private static async Task Drain(StreamReader reader, StringBuilder text, CancellationToken cancellation)
    {
        var buffer = new char[4096];
        int count;
        while ((count = await reader.ReadAsync(buffer.AsMemory(), cancellation).ConfigureAwait(false)) != 0)
        {
            lock (text) text.Append(buffer, 0, count);
        }
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
