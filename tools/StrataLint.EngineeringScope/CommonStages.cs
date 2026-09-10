using System.Diagnostics;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record TestEnvironmentContext(string Identity, string Culture, string UICulture)
{
    [System.Text.Json.Serialization.JsonIgnore] public string Launcher { get; init; } = "dotnet";
    public string WorkingDirectory { get; init; } = "";
    public string RuntimeMaterial { get; init; } = "";
    [System.Text.Json.Serialization.JsonIgnore] public string ValuesIdentity { get; init; } = "";
    [System.Text.Json.Serialization.JsonIgnore] public IDictionary<string, string?> Inherited { get; init; } = new Dictionary<string, string?>();
    [System.Text.Json.Serialization.JsonIgnore] public IDictionary<string, string?> Values { get; init; } = new Dictionary<string, string?>();
    [System.Text.Json.Serialization.JsonIgnore] public int Startups { get; init; }
    [System.Text.Json.Serialization.JsonIgnore] public double StartupSeconds { get; init; }
    internal string ForValues(bool values) => values ? ValuesIdentity : Identity;
    internal IDictionary<string, string?> Exposure(bool values) => values ? Values : Inherited;
}

internal sealed class CommonStages(string root, TextWriter output, CancellationToken deadlineCancellation = default,
    Action<Process>? processExited = null, TimeProvider? timeProvider = null)
{
    private readonly List<StageStep> steps = [];
    private string stage = "input";
    private string? candidate;

    internal static void NormalizeEnvironment(IDictionary<string, string?> environment) =>
        environment["DOTNET_CLI_UI_LANGUAGE"] = "en-US";

    internal static void InitializeTestEnvironment()
    {
        var environment = new ProcessStartInfo().Environment;
        NormalizeEnvironment(environment);
        // dotnet test applies the CLI language to its testhost. A raw runner DLL
        // needs the same UI culture; setting an environment variable alone does not.
        System.Globalization.CultureInfo.CurrentUICulture =
            System.Globalization.CultureInfo.GetCultureInfo(environment["DOTNET_CLI_UI_LANGUAGE"]!);
    }

    internal static TestEnvironmentContext TestEnvironment(string? root = null)
    {
        // Observe fresh runtime startup under the actual launch policy. Caller
        // thread cultures (including a containing testhost's) are not child inputs.
        root ??= Directory.GetCurrentDirectory();
        var inherited = new ProcessStartInfo().Environment;
        NormalizeEnvironment(inherited);
        var started = TimeProvider.System.GetTimestamp();
        var launcher = (inherited.TryGetValue("PATH", out var path) ? path ?? "" : "").Split(Path.PathSeparator)
            .Select(directory => Path.Combine(directory, OperatingSystem.IsWindows() ? "dotnet.exe" : "dotnet"))
            .FirstOrDefault(File.Exists) ?? throw new InvalidDataException("dotnet launcher is absent from PATH");
        launcher = Path.GetFullPath(launcher);
        var result = new CommonStages(root, TextWriter.Null).Capture(launcher,
            [typeof(Program).Assembly.Location, "test-environment"], environment: inherited);
        if (result.Exit != 0) throw new InvalidDataException("test environment observation failed: " + result.Text);
        var child = JsonSerializer.Deserialize<TestEnvironmentContext>(result.Text)
            ?? throw new InvalidDataException("missing test environment observation");
        root = child.WorkingDirectory;
        if (Directory.Exists(Path.Combine(root, CommonBuildOutputs.PackagesPath)))
            inherited["NUGET_PACKAGES"] = Path.Combine(root, CommonBuildOutputs.PackagesPath);
        var values = inherited.Where(pair => RuntimeVariable(pair.Key) || pair.Key.StartsWith("LC_", StringComparison.Ordinal)
            || pair.Key is "PATH" or "HOME" or "TMPDIR" or "TMP" or "TEMP" or "LANG" or "TZ" or "SystemRoot" or "WINDIR" or "NUGET_PACKAGES")
            .ToDictionary(pair => pair.Key, pair => pair.Value, StringComparer.Ordinal);
        return child with { Launcher = launcher, Inherited = inherited, Values = values, Startups = 1,
            StartupSeconds = TimeProvider.System.GetElapsedTime(started).TotalSeconds,
            ValuesIdentity = AffectedTestPlan.Digest([AffectedTestPlan.EnvironmentKey(values, child.Culture, child.UICulture, true),
                root, child.Identity, launcher, CommonExecutionEvidence.Hash(launcher), child.RuntimeMaterial]) };
    }

    internal static bool RuntimeVariable(string key) => key.StartsWith("DOTNET_", StringComparison.Ordinal)
        || key.StartsWith("COMPlus_", StringComparison.Ordinal) || key.StartsWith("VSTEST_", StringComparison.Ordinal)
        || key.StartsWith("CORECLR_", StringComparison.Ordinal) || key.StartsWith("COREHOST_", StringComparison.Ordinal)
        || key.StartsWith("LD_", StringComparison.Ordinal) || key.StartsWith("DYLD_", StringComparison.Ordinal);

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
        var clock = timeProvider ?? TimeProvider.System;
        var started = clock.GetTimestamp();
        ClearEvidence("build", "engineering", "current");
        File.Delete(Path.Combine(root, CommonExecutionEvidence.TestsPath));
        var outputs = Path.Combine(root, CommonBuildOutputs.RootPath);
        if (Directory.Exists(outputs)) Directory.Delete(outputs, recursive: true);
        Step("restore-StrataLint", "dotnet", ["restore", "tools/StrataLint.sln", "--locked-mode"]);
        var restored = clock.GetTimestamp();
        Step("build", "dotnet", ["build", "tools/StrataLint.sln", "--configuration", "Release", "--no-restore", "--warnaserror", "--verbosity", "normal",
            "-p:CustomAfterMicrosoftCommonTargets=" + Path.Combine(root, "tools/scripts/ci-build-outputs.targets"),
            "-p:ProvideCommandLineArgs=true", "-p:EmitCompilerGeneratedFiles=true", "-p:CiRepositoryRoot=" + root, "-p:CiBuildOutputRoot=" + outputs]);
        var built = clock.GetTimestamp();
        var products = CommonBuildOutputs.Collect(root);
        var collected = clock.GetTimestamp();
        var record = CommonExecutionEvidence.SealBuild(root, candidate!, products, steps.ToArray());
        CommonExecutionEvidence.Write(root, CommonExecutionEvidence.RootPath + "/build-cost.json", new {
            restore_seconds = clock.GetElapsedTime(started, restored).TotalSeconds,
            native_seconds = clock.GetElapsedTime(restored, built).TotalSeconds,
            collect_seconds = clock.GetElapsedTime(built, collected).TotalSeconds,
            seal_seconds = clock.GetElapsedTime(collected).TotalSeconds,
            build_seconds = clock.GetElapsedTime(started).TotalSeconds });
        return record;
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
        var testCoverage = CommonExecutionEvidence.Read<TestExecutionRecord>(root, CommonExecutionEvidence.TestsPath);
        if (testCoverage.Projects.All(project => project.Executed == 0))
            steps[^1] = steps[^1] with { Status = "reused" };
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

    internal (int Exit, string Text) Capture(string executable, string[] arguments, TimeSpan? defaultTimeout = null,
        IDictionary<string, string?>? environment = null)
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
        if (environment is not null)
        {
            start.Environment.Clear();
            foreach (var pair in environment) start.Environment[pair.Key] = pair.Value;
        }
        NormalizeEnvironment(start.Environment);
        if (stage != "build" && Directory.Exists(Path.Combine(root, CommonBuildOutputs.PackagesPath)))
            start.Environment["NUGET_PACKAGES"] = Path.Combine(root, CommonBuildOutputs.PackagesPath);
        foreach (var arg in arguments) start.ArgumentList.Add(arg);
        if (arguments.Contains("--build-round", StringComparer.Ordinal))
            AffectedEnvironmentObservation.Write(root, "runner-launch", launched: start.Environment);
        using var process = Process.Start(start) ?? throw new IOException("cannot start " + executable);
        using var timer = new CancellationTokenSource(timeout, clock);
        using var cancellation = CancellationTokenSource.CreateLinkedTokenSource(deadlineCancellation, timer.Token);
        var stdoutText = new StringBuilder();
        var stderrText = new StringBuilder();
        var stdout = Drain(process.StandardOutput, stdoutText, cancellation.Token);
        var stderr = Drain(process.StandardError, stderrText, cancellation.Token);
        try
        {
            process.WaitForExitAsync(cancellation.Token).GetAwaiter().GetResult();
            processExited?.Invoke(process);
            Task.WhenAll(stdout, stderr).WaitAsync(cancellation.Token).GetAwaiter().GetResult();
            cancellation.Token.ThrowIfCancellationRequested();
            return (process.ExitCode, Captured(stdoutText) + Captured(stderrText));
        }
        catch (OperationCanceledException)
        {
            try { if (!process.HasExited) process.Kill(entireProcessTree: true); }
            catch (InvalidOperationException) { } // Exit can race the kill.
            // Reaping and cancelled readers cannot keep a failed stage from reporting.
            using var cleanup = new CancellationTokenSource(TimeSpan.FromSeconds(5));
            try
            {
                Task.WhenAll(stdout, stderr, process.WaitForExitAsync(cleanup.Token))
                    .WaitAsync(cleanup.Token).GetAwaiter().GetResult();
            }
            catch (OperationCanceledException) { }
            return (124, Captured(stdoutText) + Captured(stderrText)
                + "\nstage deadline exceeded: " + executable + "\n");
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
