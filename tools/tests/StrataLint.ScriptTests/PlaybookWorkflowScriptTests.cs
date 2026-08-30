using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class PlaybookWorkflowScriptTests
{
    private const string ScriptPath = "tools/scripts/workflow/playbook-workflows.sh";

    [Fact]
    public void DeliverCheckFreezesAfterReceiptsAndBeforeReadOnlyChecks()
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
                "dotnet:ledger-append --candidate-lean-report .lake/build/stratalint/raw-lean-report.json",
                "dotnet:digest-status --base synthetic-base",
                "make:preflight BASE=synthetic-base",
                "git:diff --diff-filter=A --name-only -z synthetic-base...HEAD -- Golden/Frozen/accepted/*.json",
                "git:ls-files --others --exclude-standard -z -- Golden/Frozen/accepted/*.json",
            ],
            fixture.Calls());
    }

    [Fact]
    public void ReceiptsStagePropagatesHandwrittenStatusFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PlaybookFixture();

        var result = fixture.Run(
            "receipts-stage",
            "synthetic-base",
            dotnetFailure: "digest-status",
            dotnetDiagnostic: "RECEIPTS_STAGE_INVALID handwritten status differs from derived");

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "handwritten status differs from derived",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.Equal(
            ["make:align-digestion-status BASE=synthetic-base", "dotnet:digest-status --base synthetic-base"],
            fixture.Calls());
    }

    [Fact]
    public void ReceiptsStageRejectsAbsorbedMultiClauseAtomWithoutDecomposition()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PlaybookFixture();

        var result = fixture.Run(
            "receipts-stage",
            "synthetic-base",
            dotnetFailure: "digest-status",
            dotnetDiagnostic:
                "RECEIPTS_STAGE_INVALID atom verdict has multiple clauses, migration=absorbed, unresolved_subitems=[]");

        Assert.NotEqual(0, result.ExitCode);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("multiple clauses", error, StringComparison.Ordinal);
        Assert.Contains("unresolved_subitems=[]", error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("deliver-check")]
    [InlineData("receipts-stage")]
    [InlineData("deposit")]
    [InlineData("cover")]
    public void CanonicalPlaybookVerbNeverExecutesBranchMerge(string command)
    {
        if (OperatingSystem.IsWindows()) return;

        if (command is "deposit" or "cover")
        {
            using var fixture = new DepositCoverWorkflowScriptTests.TransactionFixture();
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
            WriteExecutable("make", "printf 'make:%s\\n' \"$*\" >> \"$PLAYBOOK_TEST_CALLS\"");
            WriteExecutable(
                "git",
                """
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
                """);
            WriteExecutable(
                "dotnet",
                "args=\"$*\"; command=${args##* -- }; printf 'dotnet:%s\\n' \"$command\" >> \"$PLAYBOOK_TEST_CALLS\"; "
                + "if [[ -n ${PLAYBOOK_DOTNET_FAILURE:-} && $command == $PLAYBOOK_DOTNET_FAILURE* ]]; then "
                + "printf '%s\\n' \"$PLAYBOOK_DOTNET_DIAGNOSTIC\" >&2; exit 1; fi");
        }

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
