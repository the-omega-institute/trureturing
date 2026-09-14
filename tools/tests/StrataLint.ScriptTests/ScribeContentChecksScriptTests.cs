using System.Globalization;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeContentChecksScriptTests
{
    [Theory]
    [InlineData(0)]
    [InlineData(29)]
    public void CacheFetcherDeltaSelectsScribeChecksAndPropagatesFailure(int childExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScribeContentFixture();

        var unchanged = fixture.RunGate(childExit);
        Assert.Equal(0, unchanged.ExitCode);
        Assert.Empty(fixture.Invocations);

        fixture.ChangeFetcher();
        var result = fixture.RunGate(childExit);

        Assert.Equal(childExit, result.ExitCode);
        Assert.Equal(
            childExit == 0 ? new[] { "projections", "describe-report" } : ["projections"],
            fixture.Invocations);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RegisteredInputChangesAndDeletionsSelectChecks(bool deleted)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScribeContentFixture();
        fixture.ChangeRegisteredInput(deleted);
        var result = fixture.RunGate(0);
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(new[] { "projections", "describe-report" }, fixture.Invocations);
    }

    [Fact]
    public void UnregisteredScriptDoesNotExpandScribeInputs()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScribeContentFixture();
        fixture.AddUnregisteredScript();
        Assert.Equal(0, fixture.RunGate(0).ExitCode);
        Assert.Empty(fixture.Invocations);
    }

    [Fact]
    public void MissingScribeRegistrationFailsSpecifically()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScribeContentFixture();
        fixture.RemoveRegistration();
        var result = fixture.RunGate(0);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("scribe-content-checks", Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("Meta/lean-report.toml", Encoding.UTF8.GetString(result.StandardError));
        Assert.Empty(fixture.Invocations);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private sealed class ScribeContentFixture : IDisposable
    {
        private const string InputHelperPath = "tools/scripts/report/lean-report-input.sh";
        private const string ContentChecksPath = "tools/scripts/workflow/scribe-content-checks.sh";
        private const string CacheInputPath = "tools/scripts/worktree/lean-cache-input.sh";
        private const string CacheFetcherPath = "tools/scripts/worktree/lean-cache-publish.sh";
        private readonly TemporaryDirectory temporary = new();
        private readonly string repository;
        private readonly string bin;
        private readonly string log;
        private readonly string report;
        private readonly string baseline;

        internal ScribeContentFixture()
        {
            repository = Path.Combine(temporary.Path, "repository");
            bin = Path.Combine(temporary.Path, "bin");
            log = Path.Combine(temporary.Path, "scribe.log");
            report = Path.Combine(temporary.Path, "raw-lean-report.json");
            ScriptHarnessScratch.EnsureDirectory(bin);
            ScriptHarnessScratch.WriteScratchText(report, "{}\n");
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), InputHelperPath), Path.Combine(repository, InputHelperPath));
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), ContentChecksPath), Path.Combine(repository, ContentChecksPath));
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), CacheInputPath), Path.Combine(repository, CacheInputPath));
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), CacheFetcherPath), Path.Combine(repository, CacheFetcherPath));
            Write("Meta/lean-report.toml", "compatibility_version = 1\n"
                + "source_patterns = [\"Trureturing.lean\", \"D5/**/*.lean\"]\n"
                + "scribe_check_inputs = [\"tools/scripts/worktree/lean-cache-publish.sh\", \"tools/Registered/**/*.cs\"]\n");
            Write("tools/Registered/Nested/Probe.cs", "// registered input\n");
            Write("tools/lean-inspector/inspect.sh", "#!/bin/bash\n");
            Write("tools/scripts/lean-report-pair.sh", "#!/bin/bash\n");
            // Synthetic producer input; no assertions depend on the repository workflow text.
            Write(".github/workflows/ci.yml", "jobs:\n  lean-inspect:\n  baseline-admission:\n");
            Write("global.json", "{}\n");
            Write("Directory.Build.props", "<Project />\n");
            Write("Directory.Packages.props", "<Project />\n");
            foreach (var project in new[]
                     { "StrataLint.Cli", "StrataLint.Engine", "StrataLint.Scribe", "StrataLint.Scribe.Documents", "Trureturing.Truth" })
            {
                Write($"tools/{project}/{project}.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
                Write($"tools/{project}/Fixture.cs", "// fixture\n");
                Write($"tools/{project}/packages.lock.json", "{}\n");
            }
            ScriptHarnessScratch.WriteExecutableStub(Path.Combine(bin, "dotnet"), """
                if [[ "$1" == scribe-fixture ]]; then
                  printf '%s\n' "$2" >> "$SCRIBE_LOG"
                  exit "$SCRIBE_EXIT"
                fi
                PATH="$ORIGINAL_PATH" exec dotnet "$@"
                """);
            RunGit("init", "--quiet");
            RunGit("config", "user.email", "stratalint@example.invalid");
            RunGit("config", "user.name", "StrataLint Tests");
            RunGit("add", ".");
            RunGit("commit", "--quiet", "-m", "scribe input fixture");
            baseline = RunGit("rev-parse", "HEAD").Trim();
        }

        internal string[] Invocations => ScriptHarnessScratch.ReadRecordedCalls(log);

        internal void ChangeFetcher() => ScriptHarnessScratch.AppendScratchText(
            Path.Combine(repository, CacheFetcherPath), "# fetch acceptance changed\n");

        internal void ChangeRegisteredInput(bool deleted)
        {
            var path = Path.Combine(repository, "tools/Registered/Nested/Probe.cs");
            if (deleted) ScriptHarnessScratch.DeleteScratchFile(path);
            else ScriptHarnessScratch.AppendScratchText(path, "// changed\n");
        }

        internal void AddUnregisteredScript() => Write("tools/scripts/unrelated.sh", "#!/bin/bash\n");
        internal void RemoveRegistration() => Write("Meta/lean-report.toml",
            "compatibility_version = 1\nsource_patterns = [\"Trureturing.lean\", \"D5/**/*.lean\"]\n");

        internal ProcessOutput RunGate(int childExit) => TestProcessRunner.Run(
            "/bin/bash",
            ["-c", "ORIGINAL_PATH=\"$PATH\" PATH=\"$1:$PATH\" SCRIBE_LOG=\"$2\" "
                + "SCRIBE_EXIT=\"$3\" STRATALINT_SCRIBE_BASE=\"$6\" "
                + "exec /bin/bash \"$4\" \"$5\" scribe-fixture",
                "scribe-fetcher-delta", bin, log, childExit.ToString(CultureInfo.InvariantCulture),
                Path.Combine(repository, ContentChecksPath), report, baseline],
            repository, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);

        private string RunGit(params string[] arguments)
        {
            var result = TestProcessRunner.Run("git", arguments, repository,
                TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput);
        }

        private void Write(string relativePath, string contents)
        {
            var path = Path.Combine(repository, relativePath);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(path)!);
            ScriptHarnessScratch.WriteScratchText(path, contents);
        }

        public void Dispose() => temporary.Dispose();
    }
}
