using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class EngineeringTestExecutionHarnessScriptTests
{
    private const string ExecutablePath = "/usr/bin:/bin:/usr/sbin:/sbin";
    private static readonly UTF8Encoding Utf8 = new(false);

    [Fact]
    public void CanonicalEngineeringScriptReceivesRepositoryRevisionsDirectly()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario());

        Assert.True(run.Process.ExitCode == 0, run.Diagnostics);
        Assert.Equal(
        [
            run.Repository,
            run.Head,
            run.Base!,
        ],
            run.EngineeringArguments);
    }

    [Fact]
    public void MissingObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.Missing,
            "missing");
    }

    [Fact]
    public void NotRegularObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.NotRegular,
            "not-regular");
    }

    [Fact]
    public void UnreadableObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.Unreadable,
            "unreadable");
    }

    [Fact]
    public void SyntaxInvalidObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.SyntaxInvalid,
            "syntax-error");
    }

    [Fact]
    public void SourceNonzeroObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.SourceNonzero,
            "source-nonzero");
    }

    [Fact]
    public void EntrypointMissingObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.EntrypointMissing,
            "entrypoint-missing");
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void AssertUnavailableAndPreservesEngineeringExitCodes(
        ObservationLibraryState observationLibraryState,
        string expectedReason)
    {
        foreach (var engineeringExitCode in new[] { 7, 0 })
        {
            using var run = RunHarness(new HarnessScenario(
                EngineeringExitCode: engineeringExitCode,
                ObservationLibraryState: observationLibraryState));

            Assert.True(run.Process.ExitCode == engineeringExitCode, run.Diagnostics);
            Assert.Contains(
                $"RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason={expectedReason}",
                run.StandardOutput,
                StringComparison.Ordinal);
            Assert.Equal(3, run.EngineeringArguments.Length);
        }
    }

    [Fact]
    public void HeadWithoutFirstParentFailsBeforeMake()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(HeadHasFirstParent: false));

        Assert.Equal(128, run.Process.ExitCode);
        Assert.Contains("HEAD^1", run.StandardError, StringComparison.Ordinal);
        Assert.Empty(run.EngineeringArguments);
    }

    [Fact]
    public void EngineeringSegmentSuccessEmitsOneCompleteCanonicalJsonLine()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario());

        Assert.Equal(0, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        var root = sentinel.RootElement;
        Assert.Equal(
        [
            "schema_version", "segment", "event", "merge_commit", "tree", "base",
            "source_head", "raw_rc", "outcome", "report_input_address", "report_sha256",
            "judge_source_address", "scribe_source_address", "selected_test_ids",
            "ordered_check_ids",
        ],
            root.EnumerateObject().Select(static property => property.Name));
        Assert.Equal("pfci-segment-evidence-v1", root.GetProperty("schema_version").GetString());
        Assert.Equal("engineering", root.GetProperty("segment").GetString());
        Assert.Equal("push", root.GetProperty("event").GetString());
        Assert.Equal(0, root.GetProperty("raw_rc").GetInt32());
        Assert.Equal("passed", root.GetProperty("outcome").GetString());
        Assert.Equal(JsonValueKind.Null, root.GetProperty("source_head").ValueKind);
        Assert.Equal(JsonValueKind.Null, root.GetProperty("report_input_address").ValueKind);
        Assert.Equal(JsonValueKind.Null, root.GetProperty("report_sha256").ValueKind);
        Assert.Equal(JsonValueKind.Null, root.GetProperty("judge_source_address").ValueKind);
        Assert.Equal(JsonValueKind.Null, root.GetProperty("scribe_source_address").ValueKind);
        Assert.Equal(
        [
            "Alpha.Tests::Class.Quote\"Case",
            "Zeta.Tests::Class.Path\\Case",
        ],
            root.GetProperty("selected_test_ids").EnumerateArray()
                .Select(static value => value.GetString()));
        Assert.Equal(
        [
            "restore-compile-fail-proofs",
            "restore-engineering-solution",
            "build-candidate",
            "engineering-tests",
            "stratalint-selftest",
            "compile-fail-proof",
            "banned-api-compile-fail-proof",
        ],
            root.GetProperty("ordered_check_ids").EnumerateArray()
                .Select(static value => value.GetString()));
        Assert.DoesNotContain(": ", run.StandardOutput, StringComparison.Ordinal);
        Assert.False(
            run.Process.StandardOutput.Length >= 3
            && run.Process.StandardOutput.AsSpan(0, 3).SequenceEqual(
                new byte[] { 0xef, 0xbb, 0xbf }));
    }

    [Fact]
    public void EngineeringSegmentKeepsRawClassesWhenMakeFoldsFailuresToTwo()
    {
        if (OperatingSystem.IsWindows()) return;
        using var candidateDirect = RunSegment(new SegmentScenario(EngineeringExitCode: 1));
        using var candidateMake = RunSegment(new SegmentScenario(
            EngineeringExitCode: 1,
            InvokeThroughMake: true));
        using var infrastructureDirect = RunSegment(new SegmentScenario(BuildExitCode: 9));
        using var infrastructureMake = RunSegment(new SegmentScenario(
            BuildExitCode: 9,
            InvokeThroughMake: true));

        Assert.Equal(1, candidateDirect.Process.ExitCode);
        Assert.Equal(2, candidateMake.Process.ExitCode);
        Assert.Equal(2, infrastructureDirect.Process.ExitCode);
        Assert.Equal(2, infrastructureMake.Process.ExitCode);
        AssertSentinel(candidateDirect, 1, "candidate-check-failed");
        AssertSentinel(candidateMake, 1, "candidate-check-failed");
        AssertSentinel(infrastructureDirect, 2, "subprocess-infrastructure-failed");
        AssertSentinel(infrastructureMake, 2, "subprocess-infrastructure-failed");
    }

    [Fact]
    public void EngineeringSegmentFailureAfterSelectionPreservesExecutedIdentities()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(
            EngineeringExitCode: 1,
            EmitEngineeringEvidenceOnFailure: true));

        Assert.Equal(1, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal(
        [
            "Alpha.Tests::Class.Quote\"Case",
            "Zeta.Tests::Class.Path\\Case",
        ],
            sentinel.RootElement.GetProperty("selected_test_ids").EnumerateArray()
                .Select(static value => value.GetString()));
    }

    [Fact]
    public void EngineeringSegmentInvalidEventFailsBeforeEvidenceSelection()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(Event: "invalid\"event\\value"));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal("invalid\"event\\value", sentinel.RootElement.GetProperty("event").GetString());
        Assert.Equal(2, sentinel.RootElement.GetProperty("raw_rc").GetInt32());
        Assert.Equal("missing-required-input", sentinel.RootElement.GetProperty("outcome").GetString());
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("merge_commit").ValueKind);
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
    }

    [Fact]
    public void EngineeringSegmentPrRequiresExactlyTwoParents()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(Event: "PR"));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal("parent-mismatch", sentinel.RootElement.GetProperty("outcome").GetString());
        Assert.Equal(2, sentinel.RootElement.GetProperty("raw_rc").GetInt32());
        Assert.Matches("^[0-9a-f]{40}$", sentinel.RootElement.GetProperty("merge_commit").GetString());
        Assert.Matches("^[0-9a-f]{40}$", sentinel.RootElement.GetProperty("tree").GetString());
        Assert.Matches("^[0-9a-f]{40}$", sentinel.RootElement.GetProperty("base").GetString());
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("source_head").ValueKind);
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
    }

    [Fact]
    public void EngineeringSegmentCompileFailProofRequiresBothStrongMarkers()
    {
        if (OperatingSystem.IsWindows()) return;
        using var missingCode = RunSegment(new SegmentScenario(IncludeCs7036: false));
        using var missingCapability = RunSegment(new SegmentScenario(IncludeMetaClear: false));

        Assert.Equal(1, missingCode.Process.ExitCode);
        Assert.Equal(1, missingCapability.Process.ExitCode);
        AssertSentinel(missingCode, 1, "candidate-check-failed");
        AssertSentinel(missingCapability, 1, "candidate-check-failed");
    }

    [Fact]
    public void EngineeringSegmentRejectsPrebuiltJudgeOutsideRepository()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(PrebuiltJudgeOutsideRepository: true));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal("invalid-path", sentinel.RootElement.GetProperty("outcome").GetString());
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("judge_source_address").ValueKind);
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
    }

    [Fact]
    public void EngineeringSegmentRejectsPrebuiltJudgeSymlinkEscapingRepository()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(PrebuiltJudgeSymlinkOutsideRepository: true));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal("invalid-path", sentinel.RootElement.GetProperty("outcome").GetString());
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("judge_source_address").ValueKind);
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
    }

    private static void AssertSentinel(SegmentRun run, int rawRc, string outcome)
    {
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal(rawRc, sentinel.RootElement.GetProperty("raw_rc").GetInt32());
        Assert.Equal(outcome, sentinel.RootElement.GetProperty("outcome").GetString());
    }

    private static JsonDocument AssertSingleSentinel(SegmentRun run)
    {
        var lines = run.StandardOutput.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.True(lines.Length == 1, run.Diagnostics);
        return JsonDocument.Parse(lines[0]);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static SegmentRun RunSegment(SegmentScenario scenario)
    {
        var temporary = new TemporaryDirectory();
        var repository = Path.Combine(temporary.Path, "candidate");
        var toolsDirectory = Path.Combine(repository, "tools");
        var scriptsDirectory = Path.Combine(toolsDirectory, "scripts");
        var workflowDirectory = Path.Combine(scriptsDirectory, "workflow");
        var libraryDirectory = Path.Combine(scriptsDirectory, "lib");
        var binDirectory = Path.Combine(temporary.Path, "bin");
        ScriptHarnessScratch.EnsureDirectory(repository);
        ScriptHarnessScratch.EnsureDirectory(workflowDirectory);
        ScriptHarnessScratch.EnsureDirectory(libraryDirectory);
        ScriptHarnessScratch.EnsureDirectory(binDirectory);
        var sourceRoot = TestRepositoryLayout.FindRoot();
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(sourceRoot, "tools", "scripts", "workflow", "segment-engineering.sh"),
            Path.Combine(workflowDirectory, "segment-engineering.sh"));
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(sourceRoot, "tools", "scripts", "lib", "segment-evidence-lib.sh"),
            Path.Combine(libraryDirectory, "segment-evidence-lib.sh"));
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(sourceRoot, "tools", "scripts", "engineering-tests.sh"),
            Path.Combine(scriptsDirectory, "engineering-tests.sh"));
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "Makefile"),
            Path.Combine(toolsDirectory, "Makefile"));

        WriteSegmentInputs(repository);
        WriteSegmentStubs(repository, binDirectory);
        RunGit(repository, "init", "--quiet");
        RunGit(repository, "config", "user.email", "segment-engineering@example.invalid");
        RunGit(repository, "config", "user.name", "Segment Engineering Tests");
        RunGit(repository, "config", "commit.gpgsign", "false");
        RunGit(repository, "config", "core.hooksPath", "/dev/null");
        RunGit(repository, "add", ".");
        RunGit(repository, "commit", "--quiet", "-m", "fixture root");
        ScriptHarnessScratch.WriteScratchText(
            Path.Combine(repository, "candidate-change.txt"),
            "candidate change\n");
        RunGit(repository, "add", ".");
        RunGit(repository, "commit", "--quiet", "-m", "candidate");

        var environment = new List<string>
        {
            "-u", "GIT_CONFIG",
            "-u", "GIT_CONFIG_PARAMETERS",
            $"PATH={binDirectory}:{ExecutablePath}",
            $"TMPDIR={temporary.Path}",
            $"REPOSITORY={repository}",
            $"EVENT={scenario.Event}",
            $"BUILD_EXIT_CODE={scenario.BuildExitCode}",
            $"ENGINEERING_EXIT_CODE={scenario.EngineeringExitCode}",
            $"EMIT_ENGINEERING_EVIDENCE_ON_FAILURE={(scenario.EmitEngineeringEvidenceOnFailure ? 1 : 0)}",
            $"SELFTEST_EXIT_CODE={scenario.SelftestExitCode}",
            $"INCLUDE_CS7036={(scenario.IncludeCs7036 ? 1 : 0)}",
            $"INCLUDE_META_CLEAR={(scenario.IncludeMetaClear ? 1 : 0)}",
            "GIT_CONFIG_GLOBAL=/dev/null",
            "GIT_CONFIG_SYSTEM=/dev/null",
            "GIT_CONFIG_NOSYSTEM=1",
        };
        if (scenario.PrebuiltJudgeOutsideRepository
            || scenario.PrebuiltJudgeSymlinkOutsideRepository)
        {
            var outsideJudge = Path.Combine(temporary.Path, "outside", "StrataLint.dll");
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(outsideJudge)!);
            ScriptHarnessScratch.WriteScratchText(outsideJudge, "not a real assembly\n");
            var judge = outsideJudge;
            if (scenario.PrebuiltJudgeSymlinkOutsideRepository)
            {
                judge = Path.Combine(repository, "cached", "StrataLint.dll");
                ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(judge)!);
                File.CreateSymbolicLink(judge, outsideJudge);
            }
            environment.Add($"JUDGE_DLL={judge}");
            environment.Add($"JUDGE_SOURCE_ADDRESS={new string('a', 64)}");
        }

        if (scenario.InvokeThroughMake)
        {
            environment.AddRange([
                "/usr/bin/make", "--no-print-directory", "-C", toolsDirectory, "engineering",
            ]);
        }
        else
        {
            environment.AddRange([
                "/bin/bash", Path.Combine(workflowDirectory, "segment-engineering.sh"),
            ]);
        }

        var process = TestProcessRunner.Run(
            "/usr/bin/env",
            environment,
            repository,
            TestBudgets.ScriptProcessHangGuard,
            256 * 1024);
        return new SegmentRun(temporary, process);
    }

    private static void WriteSegmentInputs(string repository)
    {
        foreach (var project in new[]
        {
            "tools/tests/CompileFailProof/CompileFailProof.csproj",
            "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
            "tools/StrataLint.sln",
        })
        {
            var path = Path.Combine(repository, project);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(path)!);
            ScriptHarnessScratch.WriteScratchText(path, "fixture\n");
        }
        ScriptHarnessScratch.WriteScratchText(
            Path.Combine(
                repository,
                "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"),
            "// fixture\n// banned-api-proof\n// banned-api-proof\n");
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteSegmentStubs(string repository, string binDirectory)
    {
        ScriptHarnessScratch.WriteExecutableStub(
            Path.Combine(repository, "tools/scripts/dotnet-build.sh"),
            "exit \"${BUILD_EXIT_CODE:?}\"");
        ScriptHarnessScratch.WriteExecutableStub(
            Path.Combine(repository, "tools/scripts/stratalint-selftest.sh"),
            "exit \"${SELFTEST_EXIT_CODE:?}\"");
        ScriptHarnessScratch.WriteExecutableStub(
            Path.Combine(repository, "tools/scripts/workflow/engineering-test-execution-harness.sh"),
            """
            if [[ "${ENGINEERING_EXIT_CODE:?}" -eq 0 || "${EMIT_ENGINEERING_EVIDENCE_ON_FAILURE:?}" -eq 1 ]]; then
              printf '%s\n' 'TEST_EVIDENCE_IDENTITIES selected_test_ids=["Zeta.Tests::Class.Path\\Case","Alpha.Tests::Class.Quote\"Case","Alpha.Tests::Class.Quote\"Case"]'
            fi
            exit "${ENGINEERING_EXIT_CODE:?}"
            """);
        ScriptHarnessScratch.WriteExecutableStub(
            Path.Combine(binDirectory, "dotnet"),
            """
            case "${1:-}" in
              restore)
                exit 0
                ;;
              build)
                if [[ "$*" == *"BannedApiCompileFailProof.csproj"* ]]; then
                  printf '%s\n' \
                    'BannedApiViolations.cs(2,1): error RS0030: banned' \
                    'BannedApiViolations.cs(3,1): error RS0030: banned'
                  exit 1
                fi
                if [[ "${INCLUDE_CS7036:?}" -eq 1 ]]; then
                  printf '%s\n' 'CompileFailProof.cs(1,1): error CS7036: missing capability'
                fi
                if [[ "${INCLUDE_META_CLEAR:?}" -eq 1 ]]; then
                  printf '%s\n' 'MetaClear'
                fi
                exit 1
                ;;
            esac
            exit 97
            """);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static HarnessRun RunHarness(HarnessScenario scenario)
    {
        var temporary = new TemporaryDirectory();
        var candidateRoot = Path.Combine(temporary.Path, "candidate");
        var toolsDirectory = Path.Combine(candidateRoot, "tools");
        var scriptPath = Path.Combine(
            toolsDirectory,
            "scripts",
            "workflow",
            "engineering-test-execution-harness.sh");
        var binDirectory = Path.Combine(temporary.Path, "bin");
        var engineeringArguments = Path.Combine(temporary.Path, "engineering-arguments");
        ScriptHarnessScratch.EnsureDirectory(candidateRoot);
        ScriptHarnessScratch.EnsureDirectory(toolsDirectory);
        ScriptHarnessScratch.EnsureDirectory(binDirectory);
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(AppContext.BaseDirectory, "engineering-test-execution-harness.sh"),
            scriptPath);
        ScriptHarnessScratch.WriteExecutableStub(
            Path.Combine(toolsDirectory, "scripts", "engineering-tests.sh"),
            """
            : > "${ENGINEERING_ARGUMENTS:?}"
            for argument in "$@"; do
              printf '%s\n' "$argument" >> "$ENGINEERING_ARGUMENTS"
            done
            exit "${ENGINEERING_EXIT_CODE:?}"
            """);
        var observationLibrary = Path.Combine(
            toolsDirectory,
            "scripts",
            "lib",
            "resource-observation-lib.sh");
        if (scenario.ObservationLibraryState == ObservationLibraryState.NotRegular)
        {
            ScriptHarnessScratch.EnsureDirectory(observationLibrary);
        }
        else if (scenario.ObservationLibraryState != ObservationLibraryState.Missing)
        {
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(observationLibrary)!);
            ScriptHarnessScratch.WriteScratchText(
                observationLibrary,
                scenario.ObservationLibraryState switch
                {
                    ObservationLibraryState.Available =>
                        "resource_observe_run_periodic() { \"$@\"; }\n",
                    ObservationLibraryState.Unreadable =>
                        "resource_observe_run_periodic() { \"$@\"; }\n",
                    ObservationLibraryState.SyntaxInvalid =>
                        "resource_observe_run_periodic() {\n",
                    ObservationLibraryState.SourceNonzero => "return 41\n",
                    ObservationLibraryState.EntrypointMissing => ":\n",
                    _ => throw new InvalidOperationException(
                        $"Unsupported observation library state: {scenario.ObservationLibraryState}"),
                });
        }

        RunGit(candidateRoot, "init", "--quiet");
        RunGit(candidateRoot, "config", "user.email", "engineering-harness@example.invalid");
        RunGit(candidateRoot, "config", "user.name", "Engineering Harness Tests");
        RunGit(candidateRoot, "config", "commit.gpgsign", "false");
        RunGit(candidateRoot, "config", "core.hooksPath", "/dev/null");
        RunGit(candidateRoot, "add", ".");
        RunGit(candidateRoot, "commit", "--quiet", "-m", "fixture root");
        if (scenario.HeadHasFirstParent)
        {
            ScriptHarnessScratch.WriteScratchText(
                Path.Combine(candidateRoot, "candidate-change.txt"),
                "candidate change\n");
            RunGit(candidateRoot, "add", ".");
            RunGit(candidateRoot, "commit", "--quiet", "-m", "candidate");
        }
        if (scenario.ObservationLibraryState == ObservationLibraryState.Unreadable)
        {
            File.SetUnixFileMode(observationLibrary, UnixFileMode.None);
        }

        var repository = GitText(candidateRoot, "rev-parse", "--show-toplevel");
        var head = GitText(candidateRoot, "rev-parse", "HEAD");
        var @base = scenario.HeadHasFirstParent
            ? GitText(candidateRoot, "rev-parse", "HEAD^1")
            : null;
        var environment = new List<string>
        {
            "-u", "GIT_CONFIG",
            "-u", "GIT_CONFIG_PARAMETERS",
            $"PATH={binDirectory}:{ExecutablePath}",
            $"TMPDIR={temporary.Path}",
            $"ENGINEERING_ARGUMENTS={engineeringArguments}",
            $"ENGINEERING_EXIT_CODE={scenario.EngineeringExitCode}",
            "GIT_CONFIG_GLOBAL=/dev/null",
            "GIT_CONFIG_SYSTEM=/dev/null",
            "GIT_CONFIG_NOSYSTEM=1",
        };
        environment.AddRange(["/bin/bash", scriptPath, candidateRoot]);
        var process = TestProcessRunner.Run(
            "/usr/bin/env",
            environment,
            candidateRoot,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        return new HarnessRun(
            temporary,
            process,
            repository,
            head,
            @base,
            engineeringArguments);
    }

    private static void RunGit(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/env",
            GitArguments(arguments),
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, ProcessDiagnostics(result));
    }

    private static string GitText(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/env",
            GitArguments(arguments),
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, ProcessDiagnostics(result));
        return Utf8.GetString(result.StandardOutput).Trim();
    }

    private static string[] GitArguments(IEnumerable<string> arguments) =>
    [
        "-u", "GIT_AUTHOR_NAME",
        "-u", "GIT_AUTHOR_EMAIL",
        "-u", "GIT_COMMITTER_NAME",
        "-u", "GIT_COMMITTER_EMAIL",
        "-u", "GIT_CONFIG",
        "-u", "GIT_CONFIG_PARAMETERS",
        "GIT_CONFIG_GLOBAL=/dev/null",
        "GIT_CONFIG_SYSTEM=/dev/null",
        "GIT_CONFIG_NOSYSTEM=1",
        "PATH=" + ExecutablePath,
        "/usr/bin/git",
        .. arguments,
    ];

    private static string ProcessDiagnostics(ProcessOutput process) =>
        "stdout:\n" + Utf8.GetString(process.StandardOutput)
        + "\nstderr:\n" + Utf8.GetString(process.StandardError);

    private sealed record HarnessScenario(
        int EngineeringExitCode = 0,
        ObservationLibraryState ObservationLibraryState = ObservationLibraryState.Available,
        bool HeadHasFirstParent = true);

    private sealed record SegmentScenario(
        string Event = "push",
        int BuildExitCode = 0,
        int EngineeringExitCode = 0,
        int SelftestExitCode = 0,
        bool EmitEngineeringEvidenceOnFailure = false,
        bool IncludeCs7036 = true,
        bool IncludeMetaClear = true,
        bool InvokeThroughMake = false,
        bool PrebuiltJudgeOutsideRepository = false,
        bool PrebuiltJudgeSymlinkOutsideRepository = false);

    private enum ObservationLibraryState
    {
        Available,
        Missing,
        NotRegular,
        Unreadable,
        SyntaxInvalid,
        SourceNonzero,
        EntrypointMissing,
    }

    private sealed record HarnessRun(
        TemporaryDirectory Temporary,
        ProcessOutput Process,
        string Repository,
        string Head,
        string? Base,
        string EngineeringArgumentsPath) : IDisposable
    {
        internal string Diagnostics => ProcessDiagnostics(Process);

        internal string StandardOutput => Utf8.GetString(Process.StandardOutput);

        internal string StandardError => Utf8.GetString(Process.StandardError);

        internal string[] EngineeringArguments =>
            ScriptHarnessScratch.ReadRecordedCalls(EngineeringArgumentsPath);

        public void Dispose() => Temporary.Dispose();
    }

    private sealed record SegmentRun(
        TemporaryDirectory Temporary,
        ProcessOutput Process) : IDisposable
    {
        internal string Diagnostics => ProcessDiagnostics(Process);

        internal string StandardOutput => Utf8.GetString(Process.StandardOutput);

        public void Dispose() => Temporary.Dispose();
    }
}
