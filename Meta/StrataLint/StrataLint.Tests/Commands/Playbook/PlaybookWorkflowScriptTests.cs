using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class PlaybookWorkflowScriptTests
{
    private const string ScriptPath = "Meta/StrataLint/scripts/workflow/playbook-workflows.sh";

    [Fact]
    public void ShepherdConflictClassifierDropsOnlyCutProjectionCompensation()
    {
        var root = FindRepositoryRoot();
        var script = File.ReadAllText(Path.Combine(root,
            "Meta", "StrataLint", "scripts", "shepherd", "pr-shepherd-actions.sh"));
        var classifier = script[script.IndexOf("is_derived_conflict()", StringComparison.Ordinal)..];
        classifier = classifier[..classifier.IndexOf("branch_slug()", StringComparison.Ordinal)];

        Assert.DoesNotContain("Meta/StrataLint/Generated/*", classifier, StringComparison.Ordinal);
        Assert.DoesNotContain("Generated/*", classifier, StringComparison.Ordinal);
        Assert.DoesNotContain(string.Join('/', "Evidence", "D5", "values.json"), classifier, StringComparison.Ordinal);
        Assert.DoesNotContain(string.Join('/', "Meta", "StrataLint", "Generated", "anchor-catalog.v1.json"), classifier, StringComparison.Ordinal);
        Assert.DoesNotContain(string.Join('/', "Meta", "StrataLint", "Generated", "scribe-emissions.v1.json"), classifier, StringComparison.Ordinal);
        Assert.Contains("$FROZEN_LEDGER_PATH", classifier, StringComparison.Ordinal);
    }

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
                "make:ingest BASE=synthetic-base",
                "dotnet:digest-status --base synthetic-base",
                "dotnet:ledger-append --candidate-lean-report .lake/build/stratalint/raw-lean-report.json",
                "make:emit-check BASE=synthetic-base",
                "dotnet:digest-status --base synthetic-base",
                "make:preflight BASE=synthetic-base",
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
            ["make:ingest BASE=synthetic-base", "dotnet:digest-status --base synthetic-base"],
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

    [Fact]
    public void DerivedRefreshMergesBeforeRecomputingDerivedArtifacts()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PlaybookFixture();

        var result = fixture.Run("derived-refresh", "synthetic-base");

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            [
                "git:merge --no-edit synthetic-base",
                "make:lean-report",
                "make:emit",
                "make:ingest BASE=synthetic-base",
                "dotnet:digest-status --base synthetic-base",
                "make:emit-check BASE=synthetic-base",
            ],
            fixture.Calls());
    }

    private sealed class PlaybookFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string callsPath;
        private readonly string binPath;

        internal PlaybookFixture()
        {
            var root = FindRepositoryRoot();
            callsPath = Path.Combine(temporary.Path, "calls");
            binPath = Path.Combine(temporary.Path, "bin");
            Directory.CreateDirectory(binPath);
            var scriptTarget = Path.Combine(temporary.Path, ScriptPath);
            Directory.CreateDirectory(Path.GetDirectoryName(scriptTarget)!);
            File.Copy(Path.Combine(root, ScriptPath), scriptTarget);
            WriteExecutable("make", "printf 'make:%s\\n' \"$*\" >> \"$PLAYBOOK_TEST_CALLS\"");
            WriteExecutable("git", "printf 'git:%s\\n' \"$*\" >> \"$PLAYBOOK_TEST_CALLS\"");
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
            BoundedProcessRunner.Run(
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
                TimeSpan.FromSeconds(30),
                64 * 1024);

        internal string[] Calls() => File.Exists(callsPath)
            ? File.ReadAllLines(callsPath)
            : [];

        private void WriteExecutable(string name, string body)
        {
            var path = Path.Combine(binPath, name);
            File.WriteAllText(path, "#!/usr/bin/env bash\nset -euo pipefail\n" + body + "\n", Encoding.UTF8);
            if (OperatingSystem.IsWindows()) return;
            File.SetUnixFileMode(
                path,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        public void Dispose() => temporary.Dispose();
    }

    private static string FindRepositoryRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "Makefile")))
        {
            directory = directory.Parent;
        }

        return directory?.FullName ?? throw new InvalidOperationException("repository root not found");
    }
}
