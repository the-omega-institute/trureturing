using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class EngineeringTestExecutionHarnessScriptTests
{
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
        if (scenario.CreateMergeCommit)
        {
            var primaryBranch = GitText(repository, "branch", "--show-current");
            RunGit(repository, "checkout", "--quiet", "-b", "fixture-source", "HEAD^1");
            ScriptHarnessScratch.WriteScratchText(
                Path.Combine(repository, "source-change.txt"),
                "source change\n");
            RunGit(repository, "add", ".");
            RunGit(repository, "commit", "--quiet", "-m", "source");
            RunGit(repository, "checkout", "--quiet", primaryBranch);
            RunGit(repository, "merge", "--quiet", "--no-ff", "fixture-source", "-m", "merge");
        }

        var expectedMergeCommit = GitText(repository, "rev-parse", "HEAD");
        var expectedTree = GitText(repository, "rev-parse", "HEAD^{tree}");
        var expectedBase = GitText(repository, "rev-parse", "HEAD^1");
        var expectedSourceHead = scenario.CreateMergeCommit
            ? GitText(repository, "rev-parse", "HEAD^2")
            : null;

        var environment = new List<string>
        {
            "-u", "GIT_CONFIG",
            "-u", "GIT_CONFIG_PARAMETERS",
            "-u", "EVENT",
            $"PATH={binDirectory}:{ExecutablePath}",
            $"TMPDIR={temporary.Path}",
            $"REPOSITORY={repository}",
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
        if (scenario.Event is not null)
        {
            environment.Add($"EVENT={scenario.Event}");
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
            2 * 1024 * 1024);
        return new SegmentRun(
            temporary,
            process,
            expectedMergeCommit,
            expectedTree,
            expectedBase,
            expectedSourceHead);
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

}
