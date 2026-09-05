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
        using var candidateDirect = RunSegment(new SegmentScenario(
            EngineeringExitCode: 1,
            EmitEngineeringEvidenceOnFailure: true));
        using var candidateMake = RunSegment(new SegmentScenario(
            EngineeringExitCode: 1,
            EmitEngineeringEvidenceOnFailure: true,
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
    public void EngineeringSegmentExitOneWithoutTrxIdentityEvidenceIsInfrastructure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(EngineeringExitCode: 1));

        Assert.Equal(2, run.Process.ExitCode);
        AssertSentinel(run, 2, "subprocess-infrastructure-failed");
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
    public void EngineeringSegmentPlanWithoutIdentityKeepsSelectionNull()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(EmitEngineeringPlanOnly: true));

        Assert.Equal(0, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
    }

    [Fact]
    public void EngineeringSegmentEncodesIdentityPayloadLargerThanMaxArgStrlen()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(EmitLargeEngineeringEvidence: true));

        Assert.Equal(0, run.Process.ExitCode);
        Assert.True(run.Process.StandardOutput.Length > 300 * 1024, run.Diagnostics);
        using var sentinel = AssertSingleSentinel(run);
        AssertCompleteSentinel(sentinel);
        var identities = sentinel.RootElement.GetProperty("selected_test_ids").EnumerateArray()
            .Select(static value => value.GetString()).ToArray();
        Assert.Equal(5000, identities.Length);
        Assert.Equal("Owner0000.Tests::Namespace.Class.Method0000_" + new string('x', 48), identities[0]);
        Assert.Equal("Owner4999.Tests::Namespace.Class.Method4999_" + new string('x', 48), identities[^1]);
    }

    [Fact]
    public void EngineeringSegmentMissingEvidenceLibraryStillEmitsCompleteSentinel()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(MissingEvidenceLibrary: true));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        AssertCompleteSentinel(sentinel);
        Assert.Equal("evidence-library-unavailable", sentinel.RootElement.GetProperty("outcome").GetString());
    }

    [Fact]
    public void EngineeringSegmentMalformedIdentityStillEmitsCompleteSentinel()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(EmitMalformedEngineeringEvidence: true));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        AssertCompleteSentinel(sentinel);
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
    }

    [Fact]
    public void EngineeringSegmentRecordCheckEncodingFailureStillEmitsCompleteSentinel()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(RecordCheckEncodingFails: true));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        AssertCompleteSentinel(sentinel);
        Assert.Equal(JsonValueKind.Array, sentinel.RootElement.GetProperty("ordered_check_ids").ValueKind);
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
        Assert.Equal("invalid-event", sentinel.RootElement.GetProperty("outcome").GetString());
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
    public void EngineeringSegmentCompileFailProofExitOneInfrastructureIsRawTwo()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(CompileFailInfrastructureError: true));

        Assert.Equal(2, run.Process.ExitCode);
        AssertSentinel(run, 2, "subprocess-infrastructure-failed");
    }

    [Fact]
    public void EngineeringSegmentBannedApiProofExitOneInfrastructureIsRawTwo()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(BannedApiInfrastructureError: true));

        Assert.Equal(2, run.Process.ExitCode);
        AssertSentinel(run, 2, "subprocess-infrastructure-failed");
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public void SelftestDotnetExitOneIsInfrastructureForEitherRun(int failingRun)
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSelftest(failingRun, mismatch: false);

        Assert.Equal(2, run.Process.ExitCode);
    }

    [Fact]
    public void SelftestByteMismatchIsCandidateFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSelftest(failingRun: 0, mismatch: true);

        Assert.Equal(1, run.Process.ExitCode);
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

    private static void AssertCompleteSentinel(JsonDocument sentinel) =>
        Assert.Equal(
        [
            "schema_version", "segment", "event", "merge_commit", "tree", "base",
            "source_head", "raw_rc", "outcome", "report_input_address", "report_sha256",
            "judge_source_address", "scribe_source_address", "selected_test_ids",
            "ordered_check_ids",
        ],
            sentinel.RootElement.EnumerateObject().Select(static property => property.Name));

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

        var evidenceLibrary = Path.Combine(libraryDirectory, "segment-evidence-lib.sh");
        if (scenario.MissingEvidenceLibrary)
        {
            File.Delete(evidenceLibrary);
            File.CreateSymbolicLink(evidenceLibrary, Path.Combine(temporary.Path, "missing-library.sh"));
        }
        else if (scenario.RecordCheckEncodingFails)
        {
            File.AppendAllText(
                evidenceLibrary,
                "\nsegment_evidence_array_append() { return 2; }\n",
                Utf8);
        }

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
            $"EMIT_ENGINEERING_PLAN_ONLY={(scenario.EmitEngineeringPlanOnly ? 1 : 0)}",
            $"EMIT_MALFORMED_ENGINEERING_EVIDENCE={(scenario.EmitMalformedEngineeringEvidence ? 1 : 0)}",
            $"EMIT_LARGE_ENGINEERING_EVIDENCE={(scenario.EmitLargeEngineeringEvidence ? 1 : 0)}",
            $"SELFTEST_EXIT_CODE={scenario.SelftestExitCode}",
            $"INCLUDE_CS7036={(scenario.IncludeCs7036 ? 1 : 0)}",
            $"INCLUDE_META_CLEAR={(scenario.IncludeMetaClear ? 1 : 0)}",
            $"COMPILE_FAIL_INFRASTRUCTURE_ERROR={(scenario.CompileFailInfrastructureError ? 1 : 0)}",
            $"BANNED_API_INFRASTRUCTURE_ERROR={(scenario.BannedApiInfrastructureError ? 1 : 0)}",
            "GIT_CONFIG_GLOBAL=/dev/null",
            "GIT_CONFIG_SYSTEM=/dev/null",
            "GIT_CONFIG_NOSYSTEM=1",
        };
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
            2 * 1024 * 1024);
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
            if [[ "${EMIT_ENGINEERING_PLAN_ONLY:?}" -eq 1 ]]; then
              printf '%s\n' 'ENGINEERING_TEST_PLAN state=none changed=1 selected=0 reason="fixture"'
            elif [[ "${EMIT_MALFORMED_ENGINEERING_EVIDENCE:?}" -eq 1 ]]; then
              printf '%s\n' 'ENGINEERING_TEST_PLAN state=selected changed=1 selected=1 reason="fixture"'
              printf '%s\n' 'TEST_EVIDENCE_IDENTITIES selected_test_ids=[not-json'
            elif [[ "${EMIT_LARGE_ENGINEERING_EVIDENCE:?}" -eq 1 ]]; then
              printf '%s\n' 'ENGINEERING_TEST_PLAN state=selected changed=1 selected=5000 reason="fixture"'
              /usr/bin/python3 -c 'import json; print("TEST_EVIDENCE_IDENTITIES selected_test_ids=" + json.dumps([f"Owner{i:04d}.Tests::Namespace.Class.Method{i:04d}_" + "x" * 48 for i in range(5000)], separators=(",", ":")))'
            elif [[ "${ENGINEERING_EXIT_CODE:?}" -eq 0 || "${EMIT_ENGINEERING_EVIDENCE_ON_FAILURE:?}" -eq 1 ]]; then
              printf '%s\n' 'ENGINEERING_TEST_PLAN state=selected changed=1 selected=2 reason="fixture"'
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
                  if [[ "${BANNED_API_INFRASTRUCTURE_ERROR:?}" -eq 1 ]]; then
                    printf '%s\n' 'MSBUILD : error MSB1009: Project file does not exist.'
                    exit 1
                  fi
                  printf '%s\n' \
                    'BannedApiViolations.cs(2,1): error RS0030: banned' \
                    'BannedApiViolations.cs(3,1): error RS0030: banned'
                  exit 1
                fi
                if [[ "${COMPILE_FAIL_INFRASTRUCTURE_ERROR:?}" -eq 1 ]]; then
                  printf '%s\n' 'MSBUILD : error MSB1009: Project file does not exist.'
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
    private static SegmentRun RunSelftest(int failingRun, bool mismatch)
    {
        var temporary = new TemporaryDirectory();
        var repository = Path.Combine(temporary.Path, "candidate");
        var scripts = Path.Combine(repository, "tools", "scripts");
        var bin = Path.Combine(temporary.Path, "bin");
        ScriptHarnessScratch.EnsureDirectory(scripts);
        ScriptHarnessScratch.EnsureDirectory(bin);
        ScriptHarnessScratch.EnsureDirectory(
            Path.Combine(repository, "tools", "StrataLint.Cli"));
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "scripts", "stratalint-selftest.sh"),
            Path.Combine(scripts, "stratalint-selftest.sh"));
        ScriptHarnessScratch.WriteScratchText(
            Path.Combine(repository, "tools", "StrataLint.Cli", "StrataLint.Cli.csproj"),
            "fixture\n");
        var calls = Path.Combine(temporary.Path, "dotnet-calls");
        ScriptHarnessScratch.WriteExecutableStub(
            Path.Combine(bin, "dotnet"),
            """
            calls=0
            [[ ! -f "${SELFTEST_CALLS:?}" ]] || calls="$(cat "${SELFTEST_CALLS:?}")"
            calls=$((calls + 1))
            printf '%s' "$calls" > "${SELFTEST_CALLS:?}"
            if [[ "$calls" -eq "${SELFTEST_FAILING_RUN:?}" ]]; then exit 1; fi
            if [[ "${SELFTEST_MISMATCH:?}" -eq 1 ]]; then printf 'run=%s\n' "$calls"; else printf '%s\n' stable; fi
            """);
        var process = TestProcessRunner.Run(
            "/usr/bin/env",
            [
                $"PATH={bin}:{ExecutablePath}",
                $"TMPDIR={temporary.Path}",
                $"SELFTEST_CALLS={calls}",
                $"SELFTEST_FAILING_RUN={failingRun}",
                $"SELFTEST_MISMATCH={(mismatch ? 1 : 0)}",
                "/bin/bash", Path.Combine(scripts, "stratalint-selftest.sh"),
            ],
            repository,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        return new SegmentRun(temporary, process);
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
        bool EmitEngineeringPlanOnly = false,
        bool EmitMalformedEngineeringEvidence = false,
        bool EmitLargeEngineeringEvidence = false,
        bool IncludeCs7036 = true,
        bool IncludeMetaClear = true,
        bool InvokeThroughMake = false,
        bool MissingEvidenceLibrary = false,
        bool RecordCheckEncodingFails = false,
        bool CompileFailInfrastructureError = false,
        bool BannedApiInfrastructureError = false);

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
