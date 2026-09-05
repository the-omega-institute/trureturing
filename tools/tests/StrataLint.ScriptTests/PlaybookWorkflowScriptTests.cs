using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class PlaybookWorkflowScriptTests
{
    private const string ScriptPath = "tools/scripts/workflow/playbook-workflows.sh";
    private const string SyntheticBaseSha = "0000000000000000000000000000000000000001";

    [Fact]
    public void DeliverCheckAlignsBeforeReadOnlyChecks()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PlaybookFixture();

        var result = fixture.Run("deliver-check", "synthetic-base");

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            [
                "make:lean-report",
                "make:emit",
                "make:align-digestion-status BASE=synthetic-base",
                "dotnet:digest-status --base synthetic-base",
                "git:diff --diff-filter=A --name-only -z synthetic-base...HEAD -- Golden/Frozen/accepted/*.json",
                "git:ls-files --others --exclude-standard -z -- Golden/Frozen/accepted/*.json",
                "dotnet:ledger-align --candidate-lean-report .lake/build/stratalint/raw-lean-report.json",
                "dotnet:digest-status --base synthetic-base",
                $"git:rev-parse HEAD^1",
                $"make:preflight BASE={SyntheticBaseSha}",
                "git:diff --diff-filter=A --name-only -z synthetic-base...HEAD -- Golden/Frozen/accepted/*.json",
                "git:ls-files --others --exclude-standard -z -- Golden/Frozen/accepted/*.json",
            ],
            fixture.Calls());
    }

    [Fact]
    public void DeliverCheckRegistersClosedModuleAbsentFromStateAndAccepted()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PlaybookFixture();
        const string module = "D5/S0/Carrier/NewClosed.lean";
        WriteTruthGraph(fixture, module);

        var result = fixture.Run("deliver-check", "synthetic-base");

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            $"dotnet:ledger-align --add {module} --candidate-lean-report "
                + ".lake/build/stratalint/raw-lean-report.json",
            fixture.Calls());
        Assert.True(StateFragmentExists(fixture, module));
        Assert.True(AcceptedEventMentions(fixture, module));
    }

    [Theory]
    [InlineData("deliver-check")]
    [InlineData("deposit")]
    [InlineData("cover")]
    public void CanonicalPlaybookVerbNeverExecutesBranchMerge(string command)
    {
        if (OperatingSystem.IsWindows()) return;

        if (command is "deposit" or "cover")
        {
            using var fixture = new TransactionFixture();
            fixture.ChangeFormalization();
            if (command == "cover")
            {
                var deposit = fixture.Run("deposit");
                Assert.True(deposit.ExitCode == 0, Diagnostics(deposit));
                fixture.ClearCalls();
            }

            var result = fixture.Run(command);

            Assert.True(result.ExitCode == 0, Diagnostics(result));
            Assert.DoesNotContain(
                fixture.Calls(),
                call => call.StartsWith("git-branch-merge:", StringComparison.Ordinal));
            return;
        }

        using (var fixture = new PlaybookFixture())
        {
            var result = fixture.Run(command, "synthetic-base");

            Assert.True(result.ExitCode == 0, Diagnostics(result));
            Assert.DoesNotContain(
                fixture.Calls(),
                call => call.StartsWith("git-branch-merge:", StringComparison.Ordinal));
        }
    }

    private static string Diagnostics(ProcessOutput result) =>
        "stdout:\n" + Encoding.UTF8.GetString(result.StandardOutput)
        + "\nstderr:\n" + Encoding.UTF8.GetString(result.StandardError);

    private static void WriteTruthGraph(PlaybookFixture fixture, string module) =>
        WriteTruthGraphContent(
            fixture,
            JsonSerializer.Serialize(new
            {
                truth = new
                {
                    nodes = new[] { new { repo_path = module, state = "closed" } },
                },
            }));

    private static void WriteEmptyTruthGraph(PlaybookFixture fixture) =>
        WriteTruthGraphContent(
            fixture,
            JsonSerializer.Serialize(new
            {
                truth = new
                {
                    nodes = Array.Empty<object>(),
                },
            }));

    private static void WriteTruthGraphContent(PlaybookFixture fixture, string content)
    {
        var path = Path.Combine(fixture.Temporary.Path, "Generated", "truth-graph.v1.json");
        ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(path)!);
        ScriptHarnessScratch.WriteScratchText(path, content);
    }

    private static bool StateFragmentExists(PlaybookFixture fixture, string module) =>
        new FileInfo(Path.Combine(
            fixture.Temporary.Path,
            "Golden",
            "Frozen",
            "state",
            module + ".json")).Exists;

    private static bool AcceptedEventMentions(PlaybookFixture fixture, string module) =>
        new DirectoryInfo(Path.Combine(
                fixture.Temporary.Path,
                "Golden",
                "Frozen",
                "accepted"))
            .GetFiles("*.json")
            .Any(file => ReadAcceptedEvent(file).Contains(module, StringComparison.Ordinal));

    private static string ReadAcceptedEvent(FileInfo file)
    {
        using var reader = file.OpenText();
        return reader.ReadToEnd();
    }

    private sealed class PlaybookFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string callsPath;
        private readonly string binPath;

        internal PlaybookFixture()
        {
            var root = TestRepositoryLayout.FindRoot();
            callsPath = Path.Combine(temporary.Path, "calls");
            binPath = Path.Combine(temporary.Path, "bin");
            ScriptHarnessScratch.EnsureDirectory(binPath);
            var scriptTarget = Path.Combine(temporary.Path, ScriptPath);
            ScriptHarnessScratch.CopyScriptInto(Path.Combine(root, ScriptPath), scriptTarget);
            Directory.CreateDirectory(Path.Combine(temporary.Path, "Golden", "Frozen", "accepted"));
            WriteEmptyTruthGraph(this);
            WriteExecutable("make", "printf 'make:%s\\n' \"$*\" >> \"$PLAYBOOK_TEST_CALLS\"");
            WriteExecutable(
                "git",
                $$"""
                arguments=("$@")
                index=0
                while [[ $index -lt ${#arguments[@]} ]]; do
                  token=${arguments[index]}
                  case "$token" in
                    -C|-c|--git-dir|--work-tree|--namespace|--super-prefix|--config-env)
                      index=$((index + 2))
                      ;;
                    --git-dir=*|--work-tree=*|--namespace=*|--super-prefix=*|--config-env=*)
                      index=$((index + 1))
                      ;;
                    --no-pager|--paginate|--bare|--literal-pathspecs|--no-literal-pathspecs|--glob-pathspecs|--noglob-pathspecs|--icase-pathspecs)
                      index=$((index + 1))
                      ;;
                    --)
                      index=$((index + 1))
                      break
                      ;;
                    -*) index=$((index + 1)) ;;
                    *) break ;;
                  esac
                done
                subcommand=${arguments[index]:-}
                if [[ $subcommand == merge ]]; then
                  printf 'git-branch-merge:%s\n' "${arguments[*]}" >> "$PLAYBOOK_TEST_CALLS"
                  exit 97
                fi
                printf 'git:%s\n' "${arguments[*]}" >> "$PLAYBOOK_TEST_CALLS"
                if [[ $subcommand == rev-parse && "${arguments[index+1]:-}" == HEAD^1 ]]; then
                  printf '%s\n' '{{SyntheticBaseSha}}'
                fi
                """);
            WriteExecutable(
                "dotnet",
                "args=\"$*\"; command=${args##* -- }; printf 'dotnet:%s\\n' \"$command\" >> \"$PLAYBOOK_TEST_CALLS\"; "
                + "if [[ -n ${PLAYBOOK_DOTNET_FAILURE:-} && $command == $PLAYBOOK_DOTNET_FAILURE* ]]; then "
                + "printf '%s\\n' \"$PLAYBOOK_DOTNET_DIAGNOSTIC\" >&2; exit 1; fi; "
                + "read -r -a parts <<< \"$command\"; "
                + "for ((i=1; i<${#parts[@]}; i++)); do "
                + "if [[ ${parts[i]} == --add ]]; then module=${parts[i+1]}; "
                + "state=Golden/Frozen/state/${module}.json; mkdir -p \"$(dirname \"$state\")\"; "
                + "printf '{\"statement_id\":\"sha256:%064d\"}\\n' 1 > \"$state\"; "
                + "event=Golden/Frozen/accepted/$(printf '%064d' 2).json; "
                + "printf '{\"event_hash\":\"sha256:%064d\",\"event_type\":\"Freeze\",\"payload\":{\"declaration_statement_ids\":[],\"descriptor_selector\":\"%s\",\"prerequisite_frozen_node_ids\":[],\"statement_id\":\"sha256:%064d\"},\"schema_version\":5}\\n' 2 \"$module\" 1 > \"$event\"; "
                + "fi; done");
        }

        internal TemporaryDirectory Temporary => temporary;

        internal ProcessOutput Run(
            string command,
            string baseline,
            string? dotnetFailure = null,
            string? dotnetDiagnostic = null) =>
            TestProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                    $"PLAYBOOK_TEST_CALLS={callsPath}",
                    $"PLAYBOOK_DOTNET_FAILURE={dotnetFailure}",
                    $"PLAYBOOK_DOTNET_DIAGNOSTIC={dotnetDiagnostic}",
                    "/bin/bash",
                    Path.Combine(temporary.Path, ScriptPath),
                    command,
                    baseline,
                ],
                temporary.Path,
                BoundedProcessRunner.HangDetectionBudget,
                64 * 1024);

        internal string[] Calls() => ScriptHarnessScratch.ReadRecordedCalls(callsPath);

        private void WriteExecutable(string name, string body)
        {
            if (OperatingSystem.IsWindows()) return;
            ScriptHarnessScratch.WriteExecutableStub(Path.Combine(binPath, name), body);
        }

        public void Dispose() => temporary.Dispose();
    }

}
