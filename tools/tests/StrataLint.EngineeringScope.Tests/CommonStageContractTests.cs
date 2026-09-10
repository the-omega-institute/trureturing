using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class CommonStageContractTests
{
    [Theory]
    [InlineData(0, 0, "executed")]
    [InlineData(7, 2, "failed")]
    public void RealCommandPreservesExitAndBothOutputStreams(int commandExit, int rawExit, string status)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        PrepareCurrent(fixture);
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, "build/producer.sh"), $"""
            printf 'producer-out-without-newline'
            printf 'producer-error-without-newline' >&2
            exit {commandExit}
            """);
        using var output = new StringWriter();
        // Successful production is followed by the independent missing-report check.
        Assert.Equal(2, new CommonStages(fixture.Root, output).Run("current", null));
        using var summary = System.Text.Json.JsonDocument.Parse(TemporaryFileSystem.File.ReadAllText(
            Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath, "current-result.json")));
        var step = Assert.Single(summary.RootElement.GetProperty("steps").EnumerateArray());
        Assert.Equal(rawExit, step.GetProperty("raw_exit").GetInt32());
        Assert.Equal(rawExit, step.GetProperty("exit").GetInt32());
        Assert.Equal(status, step.GetProperty("status").GetString());
        var log = TemporaryFileSystem.File.ReadAllText(Path.Combine(fixture.Root, step.GetProperty("log").GetString()!));
        const string captured = "producer-out-without-newlineproducer-error-without-newline";
        if (commandExit == 0) Assert.Equal(captured, log);
        else Assert.StartsWith(captured, log, StringComparison.Ordinal);
        Assert.DoesNotContain("stage deadline exceeded", log, StringComparison.Ordinal);
    }

    [Fact]
    public void CancelledDeadlineBeforeStartupLeavesAllStepsUnexecuted()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        PrepareCurrent(fixture);
        using var deadline = new CancellationTokenSource();
        deadline.Cancel();
        using var output = new StringWriter();
        Assert.Equal(2, new CommonStages(fixture.Root, output, deadline.Token).Run("current", null));
        using var summary = System.Text.Json.JsonDocument.Parse(TemporaryFileSystem.File.ReadAllText(
            Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath, "current-result.json")));
        Assert.Equal("PREFLIGHT_BUDGET_EXHAUSTED owner=outer-deadline", summary.RootElement.GetProperty("error").GetString());
        Assert.Empty(summary.RootElement.GetProperty("steps").EnumerateArray());
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" },
            summary.RootElement.GetProperty("not_executed").EnumerateArray().Select(value => value.GetString()));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, "build/producer-started")));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public Task CancellationDuringPostExitDrainIsNotIgnoredAfterPipeRelease(bool standardError) =>
        VerifyPostExitDrainCancellation(standardError, releaseBeforeSummary: true);

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public Task CancellationDuringPostExitDrainReturnsBeforePipeHolderIsReleased(bool standardError) =>
        VerifyPostExitDrainCancellation(standardError, releaseBeforeSummary: false);

    private static async Task VerifyPostExitDrainCancellation(bool standardError, bool releaseBeforeSummary)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        PrepareCurrent(fixture);
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, "build/producer.sh"), $$"""
            set -euo pipefail
            mkfifo build/helper-ready build/helper-release
            printf 'producer-stdout\n'
            printf 'producer-stderr\n' >&2
            /bin/bash -c '
              exec {{(standardError ? ">/dev/null" : "2>/dev/null")}}
              printf "ready\n" > build/helper-ready
              read -r release < build/helper-release
            ' &
            printf '%s\n' "$!" > build/helper-pid
            read -r ready < build/helper-ready
            """);
        var exited = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var drain = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        using var deadline = new CancellationTokenSource();
        using var output = new StringWriter();
        System.Diagnostics.Process? helper = null;
        var helperPid = Path.Combine(fixture.Root, "build/helper-pid");
        var run = Task.Run(() => new CommonStages(fixture.Root, output, deadline.Token, process =>
        {
            Assert.True(process.HasExited);
            Assert.Equal(0, process.ExitCode);
            exited.TrySetResult();
            drain.Task.GetAwaiter().GetResult();
        }).Run("current", null));
        try
        {
            await exited.Task.WaitAsync(TestBudgets.ScriptProcessHangGuard);
            helper = System.Diagnostics.Process.GetProcessById(int.Parse(TemporaryFileSystem.File.ReadAllText(
                helperPid), System.Globalization.CultureInfo.InvariantCulture));
            Assert.False(helper.HasExited);
            deadline.Cancel();
            if (releaseBeforeSummary)
                TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, "build/helper-release"), "release\n");
            drain.TrySetResult();
            Assert.Equal(2, await run.WaitAsync(TestBudgets.ScriptProcessHangGuard));
            using var summary = System.Text.Json.JsonDocument.Parse(TemporaryFileSystem.File.ReadAllText(
                Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath, "current-result.json")));
            Assert.Equal(2, summary.RootElement.GetProperty("exit").GetInt32());
            var step = Assert.Single(summary.RootElement.GetProperty("steps").EnumerateArray());
            Assert.Equal("lean-report", step.GetProperty("name").GetString());
            Assert.Equal(124, step.GetProperty("raw_exit").GetInt32());
            Assert.Equal(2, step.GetProperty("exit").GetInt32());
            Assert.Equal("failed", step.GetProperty("status").GetString());
            var log = TemporaryFileSystem.File.ReadAllText(Path.Combine(fixture.Root, step.GetProperty("log").GetString()!));
            Assert.Contains("producer-stdout", log, StringComparison.Ordinal);
            Assert.Contains("producer-stderr", log, StringComparison.Ordinal);
            Assert.Contains("stage deadline exceeded", log, StringComparison.Ordinal);
            Assert.Equal(new[] { "scribe", "filemap", "check-current" }, summary.RootElement.GetProperty("not_executed")
                .EnumerateArray().Select(value => value.GetString()));
            using var printed = System.Text.Json.JsonDocument.Parse(output.ToString()
                .Split('\n', StringSplitOptions.RemoveEmptyEntries).Last());
            Assert.Equal(2, printed.RootElement.GetProperty("exit").GetInt32());
            var printedStep = System.Text.Json.JsonSerializer.Deserialize<StageStep>(
                Assert.Single(printed.RootElement.GetProperty("steps").EnumerateArray()));
            Assert.Equal(124, printedStep!.RawExit);
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
            if (!releaseBeforeSummary) Assert.False(helper.HasExited);
        }
        catch (TimeoutException exception)
        {
            throw new SkipException("infrastructure-hang-guard expired for post-exit drain fixture: " + exception.Message);
        }
        finally
        {
            deadline.Cancel();
            drain.TrySetResult();
            if (helper is null && TemporaryFileSystem.File.Exists(helperPid))
            {
                try { helper = System.Diagnostics.Process.GetProcessById(int.Parse(TemporaryFileSystem.File.ReadAllText(
                    helperPid), System.Globalization.CultureInfo.InvariantCulture)); }
                catch (ArgumentException) { } // The helper may already have exited.
            }
            try
            {
                if (helper is not null)
                {
                    try { if (!helper.HasExited) helper.Kill(); }
                    catch (InvalidOperationException) { }
                    await helper.WaitForExitAsync().WaitAsync(TestBudgets.ScriptProcessHangGuard);
                    Assert.True(helper.HasExited);
                }
                await run.WaitAsync(TestBudgets.ScriptProcessHangGuard);
            }
            catch (TimeoutException exception)
            {
                throw new SkipException("infrastructure-hang-guard expired during post-exit fixture cleanup: " + exception.Message);
            }
            finally { helper?.Dispose(); }
        }
    }

    [Fact]
    public async Task TimedOutStartedStepRetainsOutputAndIsReportedAsFailed()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        PrepareCurrent(fixture);
        var started = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        using var watcher = new FileSystemWatcher(Path.Combine(fixture.Root, "build"), "producer-started");
        watcher.Created += (_, _) => started.TrySetResult();
        watcher.EnableRaisingEvents = true;
        using var deadline = new CancellationTokenSource();
        using var output = new StringWriter();
        var run = Task.Run(() => new CommonStages(fixture.Root, output, deadline.Token).Run("current", null));
        try
        {
            await started.Task.WaitAsync(TestBudgets.ScriptProcessHangGuard);
            deadline.Cancel();
            Assert.Equal(2, await run.WaitAsync(TestBudgets.ScriptProcessHangGuard));
        }
        catch (TimeoutException exception)
        {
            throw new SkipException("infrastructure-hang-guard expired for current stage fixture: " + exception.Message);
        }
        finally
        {
            deadline.Cancel();
            await run;
        }
        using var summary = System.Text.Json.JsonDocument.Parse(TemporaryFileSystem.File.ReadAllText(
            Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath, "current-result.json")));
        Assert.Equal(2, summary.RootElement.GetProperty("exit").GetInt32());
        var step = Assert.Single(summary.RootElement.GetProperty("steps").EnumerateArray());
        Assert.Equal("lean-report", step.GetProperty("name").GetString());
        Assert.Equal(124, step.GetProperty("raw_exit").GetInt32());
        Assert.Equal(2, step.GetProperty("exit").GetInt32());
        Assert.Equal("failed", step.GetProperty("status").GetString());
        var log = TemporaryFileSystem.File.ReadAllText(Path.Combine(fixture.Root, step.GetProperty("log").GetString()!));
        Assert.Contains("producer-started", log, StringComparison.Ordinal);
        Assert.Contains("producer-stderr", log, StringComparison.Ordinal);
        var diagnostics = Path.Combine(fixture.Root, "build/ci/logs/current/lean-inspector");
        Assert.Equal("raw build progress\n", TemporaryFileSystem.File.ReadAllText(Path.Combine(diagnostics, "build.stdout.log")));
        Assert.Equal("raw inspector diagnostic\n", TemporaryFileSystem.File.ReadAllText(Path.Combine(diagnostics, "inspect.stderr.log")));
        Assert.Equal(new[] { "scribe", "filemap", "check-current" }, summary.RootElement.GetProperty("not_executed")
            .EnumerateArray().Select(value => value.GetString()));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
    }

    [Fact]
    public async Task ExpiredDeadlineBeforeStartupLeavesAllStepsUnexecuted()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        PrepareCurrent(fixture);
        var start = new System.Diagnostics.ProcessStartInfo(Path.Combine(
            Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope"))
        {
            WorkingDirectory = fixture.Root, RedirectStandardOutput = true, RedirectStandardError = true,
        };
        foreach (var argument in new[] { "current", "--repository", fixture.Root }) start.ArgumentList.Add(argument);
        start.Environment["PREFLIGHT_DEADLINE_AT"] = "0";
        using var process = System.Diagnostics.Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        try
        {
            await process.WaitForExitAsync().WaitAsync(TestBudgets.ScriptProcessHangGuard);
            var output = await stdout + await stderr;
            Assert.True(process.ExitCode == 2, output);
        }
        catch (TimeoutException exception)
        {
            throw new SkipException("infrastructure-hang-guard expired for expired stage fixture: " + exception.Message);
        }
        finally
        {
            if (!process.HasExited) { process.Kill(entireProcessTree: true); process.WaitForExit(); }
        }
        using var summary = System.Text.Json.JsonDocument.Parse(TemporaryFileSystem.File.ReadAllText(
            Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath, "current-result.json")));
        Assert.Equal(2, summary.RootElement.GetProperty("exit").GetInt32());
        Assert.Equal("PREFLIGHT_BUDGET_EXHAUSTED owner=outer-deadline", summary.RootElement.GetProperty("error").GetString());
        Assert.Empty(summary.RootElement.GetProperty("steps").EnumerateArray());
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" },
            summary.RootElement.GetProperty("not_executed").EnumerateArray().Select(value => value.GetString()));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, "build/producer-started")));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
    }

    internal static void PrepareCurrent(CurrentExecutionContractTests.CandidateFixture fixture)
    {
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, "Makefile"), "lean-report:\n\t@/bin/bash build/producer.sh\n");
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(fixture.Root, "build"));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, "build/producer.sh"), """
            set -euo pipefail
            if [[ -n "${STRATALINT_LEAN_REPORT_LOG_DIR:-}" ]]; then
              mkdir -p "$STRATALINT_LEAN_REPORT_LOG_DIR"
              printf 'raw build progress\n' > "$STRATALINT_LEAN_REPORT_LOG_DIR/build.stdout.log"
              printf 'raw inspector diagnostic\n' > "$STRATALINT_LEAN_REPORT_LOG_DIR/inspect.stderr.log"
            fi
            mkfifo build/producer-wait
            printf 'producer-started\n'
            printf 'producer-stderr\n' >&2
            : > build/producer-started
            read -r release < build/producer-wait
            """);
        var binaries = new[] { CommonExecutionEvidence.CliPath, CommonExecutionEvidence.ScribePath,
            CommonExecutionEvidence.RunnerPath, CommonExecutionEvidence.LeanProducerPath };
        foreach (var binary in binaries)
        {
            var full = Path.Combine(fixture.Root, binary);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            TemporaryFileSystem.File.WriteAllText(full, "fixture binary");
        }
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) => { fixture.WriteTrx(results, "Passed"); return 0; }, TextWriter.Null));
        var candidate = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath).Candidate;
        CiTransportTests.SealEngineering(fixture.Root, candidate, binaries, CommonExecutionEvidence.EngineeringSteps
            .Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", binaries[0])).ToArray());
    }

    [Fact]
    public void EngineeringEvidenceSurvivesLeanCacheReplacement()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) => { fixture.WriteTrx(results, "Passed"); return 0; }, TextWriter.Null));
        var log = CommonExecutionEvidence.RootPath + "/fixture.log";
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, log), "executed\n");
        var candidate = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath).Candidate;
        CiTransportTests.SealEngineering(fixture.Root, candidate, [log], CommonExecutionEvidence.EngineeringSteps
            .Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", log)).ToArray());
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(fixture.Root, ".lake"));
        TemporaryFileSystem.Directory.Delete(Path.Combine(fixture.Root, ".lake"), recursive: true);
        CommonExecutionEvidence.ValidateEngineering(fixture.Root);
    }

    [Fact]
    public void FreshEngineeringStartsLockedRestoreBeforeReportingMissingSolution()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        using var output = new StringWriter();
        Assert.Equal(1, new CommonStages(fixture.Root, output).Run("engineering", null));
        var summary = TemporaryFileSystem.File.ReadAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath, "build-result.json"));
        Assert.Contains("restore-StrataLint", summary, StringComparison.Ordinal);
        Assert.True(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.RootPath, "logs/build/restore-StrataLint.log")));
    }

    [Fact]
    public void CurrentConsumerRejectsMissingReportAndChangedDll()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) => { fixture.WriteTrx(results, "Passed"); return 0; }, TextWriter.Null));
        var dll = CommonExecutionEvidence.RootPath + "/fixture.dll";
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, dll), "candidate binary");
        var steps = CommonExecutionEvidence.EngineeringSteps.Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", dll)).ToArray();
        var candidate = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath).Candidate;
        CiTransportTests.SealEngineering(fixture.Root, candidate, [dll], steps);
        CommonExecutionEvidence.ValidateEngineering(fixture.Root);
        var currentSteps = CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", dll)).ToArray();
        Assert.ThrowsAny<IOException>(() => CommonExecutionEvidence.SealCurrent(fixture.Root, CommonExecutionEvidence.ValidateBuild(fixture.Root), currentSteps));
        TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, dll), "stale");
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateEngineering(fixture.Root));
    }

    [Theory]
    [InlineData(0, "", false)]
    [InlineData(1, "error MSB1009: Project file does not exist.", false)]
    [InlineData(1, "MissingCapability.cs(13,9): error CS7036: missing metaClear", true)]
    [InlineData(1, "MissingCapability.cs(13,9): error CS7036: missing unrelatedArgument", false)]
    [InlineData(127, "MissingCapability.cs(13,9): error CS7036: missing metaClear", false)]
    public void NegativeProofRequiresExpectedDiagnostic(int exit, string output, bool accepted) =>
        Assert.Equal(accepted, CompilationProof.ValidateCapability(exit, output));

    [Theory]
    [InlineData(0, 0)]
    [InlineData(1, 1)]
    [InlineData(2, 2)]
    [InlineData(3, 0)]
    [InlineData(19, 2)]
    [InlineData(124, 2)]
    public void StageExitNormalizationPreservesCheckFailureAndRejectsUnknown(int raw, int expected) =>
        Assert.Equal(expected, CommonStages.Normalize(raw, allowProtectedAnnotation: true));

    [Fact]
    public void ProtectedAnnotationCannotPassAnOrdinaryCommonStep() =>
        Assert.Equal(2, CommonStages.Normalize(3, allowProtectedAnnotation: false));

    [Theory]
    [InlineData("transport")]
    [InlineData("invalid-archive-before-seal")]
    [InlineData("missing-report")]
    [InlineData("invalid-report")]
    [InlineData("missing-materials")]
    [InlineData("missing-compile-metadata")]
    [InlineData("round")]
    [InlineData("missing-step")]
    [InlineData("failed-step")]
    [InlineData("missing-base-project")]
    public void CompleteCommonArtifactsValidateAfterTransportAndRejectIncompleteEvidence(string scenario)
    {
        using var source = new CurrentExecutionContractTests.CandidateFixture();
        using var target = new CurrentExecutionContractTests.CandidateFixture();
        Assert.Equal(0, Program.RunCurrentTests(source.Root, (_, results) => { source.WriteTrx(results, "Passed"); return 0; }, TextWriter.Null));
        const string log = CommonExecutionEvidence.RootPath + "/fixture.log";
        TemporaryFileSystem.File.WriteAllText(Path.Combine(source.Root, log), "executed\n");
        var engineeringSteps = CommonExecutionEvidence.EngineeringSteps.Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", log)).ToArray();
        var candidate = CommonExecutionEvidence.Read<TestExecutionRecord>(source.Root, CommonExecutionEvidence.TestsPath).Candidate;
        CiTransportTests.SealEngineering(source.Root, candidate, [log], engineeringSteps);
        var report = Path.Combine(source.Root, CommonExecutionEvidence.ReportPath);
        CiTransportTests.Report(source.Root);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        TemporaryFileSystem.File.WriteAllText(report, "{\"modules\": [], \"schema\": \"stratalint-raw-lean-report-v2\"}\n");
        using (var archive = new MemoryStream())
        {
            using (new System.IO.Compression.ZipArchive(archive, System.IO.Compression.ZipArchiveMode.Create, leaveOpen: true)) { }
            TemporaryFileSystem.File.WriteAllBytes(report + ".materials.zip", archive.ToArray());
        }
        var currentSteps = CommonExecutionEvidence.CurrentSteps.Select(name => new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", log)).ToArray();
        if (scenario == "invalid-archive-before-seal")
        {
            TemporaryFileSystem.File.WriteAllText(report + ".materials.zip", "not a ZIP archive");
            Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.SealCurrent(source.Root, CommonExecutionEvidence.ValidateBuild(source.Root), currentSteps));
            return;
        }
        CommonExecutionEvidence.SealCurrent(source.Root, CommonExecutionEvidence.ValidateBuild(source.Root), currentSteps);
        var bundle = (TemporaryFileSystem.File.ReadAllText(Path.Combine(source.Root, CommonExecutionEvidence.BundleListPath("current")))
            + TemporaryFileSystem.File.ReadAllText(Path.Combine(source.Root, CommonExecutionEvidence.BundleListPath("engineering"))))
            .Split('\0', StringSplitOptions.RemoveEmptyEntries);
        var files = bundle.SelectMany(relative =>
        {
            var full = Path.Combine(source.Root, relative);
            return TemporaryFileSystem.Directory.Exists(full)
                ? TemporaryFileSystem.Directory.EnumerateFiles(full, "*", SearchOption.AllDirectories)
                : [full];
        });
        foreach (var file in files)
        {
            var destination = Path.Combine(target.Root, Path.GetRelativePath(source.Root, file));
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            TemporaryFileSystem.File.WriteAllBytes(destination, TemporaryFileSystem.File.ReadAllBytes(file));
        }
        CommonExecutionEvidence.ValidateCommon(target.Root, [CurrentExecutionContractTests.CandidateFixture.First]);
        var current = CommonExecutionEvidence.Read<CommonStageRecord>(target.Root, CommonExecutionEvidence.CurrentPath);
        switch (scenario)
        {
            case "transport": return;
            case "missing-report": TemporaryFileSystem.File.Delete(Path.Combine(target.Root, CommonExecutionEvidence.ReportPath)); break;
            case "invalid-report": TemporaryFileSystem.File.WriteAllText(Path.Combine(target.Root, CommonExecutionEvidence.ReportPath), "invalid"); break;
            case "missing-materials": TemporaryFileSystem.File.Delete(Path.Combine(target.Root, CommonExecutionEvidence.ReportPath + ".materials.zip")); break;
            case "missing-compile-metadata": TemporaryFileSystem.Directory.Delete(Path.Combine(target.Root, "build/ci/compile-metadata"), recursive: true); break;
            case "round": CommonExecutionEvidence.Write(target.Root, CommonExecutionEvidence.CurrentPath, current with { Round = "another-round" }); break;
            case "missing-step": CommonExecutionEvidence.Write(target.Root, CommonExecutionEvidence.CurrentPath, current with { Steps = current.Steps.Skip(1).ToArray() }); break;
            case "failed-step": CommonExecutionEvidence.Write(target.Root, CommonExecutionEvidence.CurrentPath, current with { Steps = current.Steps.Select(step => step with { Exit = 1, Status = "failed" }).ToArray() }); break;
        }
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateCommon(target.Root,
            scenario == "missing-base-project" ? ["tools/tests/Removed/Removed.csproj"] : []));
    }
}
