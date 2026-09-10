using System.Diagnostics;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class PreflightProcessContractTests
{
    [Fact]
    public void FailedCurrentDiagnosticsSurvivePrCandidateCleanupWithoutSuccessfulEvidence()
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        fixture.Write(".gitignore", "build/\n");
        fixture.Write("tools/scripts/ci-stage.sh", """
            #!/bin/bash
            mkdir -p build/ci
            printf 'build/ci/engineering-paths.nul\0' > build/ci/engineering-paths.nul
            if [[ "$1" == current ]]; then
              mkdir -p build/ci/logs/current/lean-inspector
              printf 'raw cold build output\n' > build/ci/logs/current/lean-inspector/build.stdout.log
              printf '{"stage":"current","exit":2}\n' > build/ci/current-result.json
              exit 124
            fi
            """);
        fixture.Commit();
        var result = fixture.Preflight("pr", fixture.Git("rev-parse", "HEAD").Trim());
        Assert.Equal(2, result.Exit);
        var lines = result.Text.Split('\n');
        var candidate = lines.Single(line => line.StartsWith("PREFLIGHT_CANDIDATE path=", StringComparison.Ordinal))["PREFLIGHT_CANDIDATE path=".Length..];
        Assert.False(TemporaryFileSystem.Directory.Exists(candidate));
        var archive = lines.Single(line => line.StartsWith("PREFLIGHT_ARTIFACT bundle=", StringComparison.Ordinal))["PREFLIGHT_ARTIFACT bundle=".Length..];
        using var gzip = new System.IO.Compression.GZipStream(File.OpenRead(archive), System.IO.Compression.CompressionMode.Decompress);
        using var tar = new System.Formats.Tar.TarReader(gzip);
        var entries = new Dictionary<string, string>();
        while (tar.GetNextEntry() is { } entry)
            if (entry.DataStream is { } data)
                entries.Add(entry.Name, new StreamReader(data).ReadToEnd());
        Assert.Equal("raw cold build output\n", entries["build/ci/logs/current/lean-inspector/build.stdout.log"]);
        Assert.DoesNotContain("build/ci/current.json", entries.Keys);
        Assert.DoesNotContain(CommonExecutionEvidence.ReportPath, entries.Keys);
    }

    [Fact]
    public void DefaultPushRunsCommonStagesOnceWithoutParentOrRemote()
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        var result = fixture.Preflight("push", "");
        Assert.Equal(0, result.Exit);
        Assert.Equal(new[] { "engineering", "current" }, fixture.Calls());
    }

    [Fact]
    public void DivergentPrChecksSynthesizedTreeAndCleansCandidate()
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        var fork = fixture.Git("rev-parse", "HEAD").Trim();
        fixture.Write("base-only", "base data");
        fixture.Commit();
        var basis = fixture.Git("rev-parse", "HEAD").Trim();
        fixture.Git("checkout", "--detach", fork);
        fixture.Write("head-only", "candidate data");
        fixture.Commit();
        var result = fixture.Preflight("pr", basis);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(new[] { "engineering", "current", "delta" }, fixture.Calls());
        Assert.Contains("merged=yes", result.Text, StringComparison.Ordinal);
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, "base-only")));
        Assert.Empty(fixture.Git("status", "--porcelain"));
        var candidateLine = result.Text.Split('\n').Single(line => line.StartsWith("PREFLIGHT_CANDIDATE path=", StringComparison.Ordinal));
        Assert.False(TemporaryFileSystem.Directory.Exists(candidateLine["PREFLIGHT_CANDIDATE path=".Length..]));
    }

    [Theory]
    [InlineData("", false)]
    [InlineData("dev", false)]
    [InlineData("0000000000000000000000000000000000000000", false)]
    [InlineData("HEAD", true)]
    public void InvalidBaseOrUntrackedInputRejectsBeforeStages(string basis, bool dirty)
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        if (basis == "HEAD") basis = fixture.Git("rev-parse", "HEAD").Trim();
        if (dirty) fixture.Write("untracked", "dirty");
        Assert.Equal(2, fixture.Preflight("pr", basis).Exit);
        Assert.Empty(fixture.Calls());
    }

    [Theory]
    [InlineData(1)]
    [InlineData(128)]
    public void FailedCleanlinessObservationRejectsBeforeMergeAndStages(int statusExit)
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        var basis = fixture.Git("rev-parse", "HEAD").Trim();
        fixture.FailStatus(statusExit);
        var result = fixture.Preflight("pr", basis);
        Assert.True(result.Exit == 2,
            $"{result.Text}\nGit calls: {string.Join(",", fixture.GitCalls())}; stages: {string.Join(",", fixture.Calls())}");
        Assert.Contains("status observation failed", result.Error, StringComparison.Ordinal);
        Assert.Contains("PREFLIGHT_RESULT mode=pr stage=input exit=2 raw_exit=2 reason=status-observation-failed",
            result.Text, StringComparison.Ordinal);
        Assert.Equal(new[] { "status" }, fixture.GitCalls());
        Assert.Empty(fixture.Calls());
    }

    [Fact]
    public void ConflictStopsBeforeExecutingCandidate()
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        fixture.Write("conflict", "original"); fixture.Commit();
        var fork = fixture.Git("rev-parse", "HEAD").Trim();
        fixture.Write("conflict", "base"); fixture.Commit();
        var basis = fixture.Git("rev-parse", "HEAD").Trim();
        fixture.Git("checkout", "--detach", fork);
        fixture.Write("conflict", "head"); fixture.Commit();
        var result = fixture.Preflight("pr", basis);
        Assert.Equal(1, result.Exit);
        Assert.Empty(fixture.Calls());
    }

    [Theory]
    [InlineData("1", 1)]
    [InlineData("19", 2)]
    [InlineData("3", 2)]
    public void CommonFailureStopsLaterStagesAndNormalizesExit(string raw, int expected)
    {
        using var fixture = new Fixture(File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")));
        Assert.Equal(expected, fixture.Preflight("push", "", raw).Exit);
        Assert.Equal(new[] { "engineering" }, fixture.Calls());
    }

    private sealed class Fixture : IDisposable
    {
        private readonly string scratch = TemporaryFileSystem.Directory.CreateTempSubdirectory("preflight-contract-").FullName;
        internal string Root => Path.Combine(scratch, "repository");
        private string CallsPath => Path.Combine(scratch, "calls");
        private string GitCallsPath => Path.Combine(scratch, "git-calls");
        private string? gitBin;
        private string? realGit;
        internal Fixture(string preflightScript)
        {
            TemporaryFileSystem.Directory.CreateDirectory(Root);
            Write("tools/scripts/preflight.sh", preflightScript);
            Write("tools/scripts/ci-stage.sh", """
                #!/bin/bash
                printf '%s\n' "$1" >> "$CONTRACT_CALLS"
                if [[ -f base-only && -f head-only ]]; then printf 'merged=yes\n'; fi
                exit "${CONTRACT_EXIT:-0}"
                """);
            Git("init", "-q"); Git("config", "user.name", "Fixture"); Git("config", "user.email", "fixture@example.invalid");
            Commit();
        }
        internal void Write(string path, string text)
        {
            var full = Path.Combine(Root, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            TemporaryFileSystem.File.WriteAllText(full, text);
        }
        internal void Commit() { Git("add", "."); Git("commit", "-qm", "fixture"); }
        internal void FailStatus(int exit)
        {
            realGit = Run("/bin/bash", ["-c", "command -v git"]).Text.Trim();
            gitBin = Path.Combine(scratch, "bin");
            TemporaryFileSystem.Directory.CreateDirectory(gitBin);
            var shim = Path.Combine(gitBin, "git");
            TemporaryFileSystem.File.WriteAllText(shim, $$"""
                #!/bin/bash
                case "$1" in
                  status)
                    printf 'status\n' >> "$CONTRACT_GIT_CALLS"
                    printf 'status observation failed\n' >&2
                    exit {{exit}}
                    ;;
                  merge-tree) printf 'merge-tree\n' >> "$CONTRACT_GIT_CALLS" ;;
                esac
                exec "$CONTRACT_REAL_GIT" "$@"
                """);
            if (!OperatingSystem.IsWindows())
                File.SetUnixFileMode(shim, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }
        internal string Git(params string[] args)
        {
            var result = Run("git", args);
            Assert.True(result.Exit == 0, result.Text);
            return result.Text;
        }
        internal (int Exit, string Text, string Error) Preflight(string mode, string basis, string raw = "0")
        {
            var environment = new Dictionary<string, string> { ["MODE"] = mode, ["BASE"] = basis, ["CONTRACT_CALLS"] = CallsPath, ["CONTRACT_EXIT"] = raw };
            if (gitBin is not null)
            {
                environment["PATH"] = gitBin + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH");
                environment["CONTRACT_REAL_GIT"] = realGit!;
                environment["CONTRACT_GIT_CALLS"] = GitCallsPath;
            }
            return Run("/bin/bash", ["tools/scripts/preflight.sh"], environment);
        }
        internal string[] Calls() => TemporaryFileSystem.File.Exists(CallsPath) ? TemporaryFileSystem.File.ReadAllText(CallsPath).Split('\n', StringSplitOptions.RemoveEmptyEntries) : [];
        internal string[] GitCalls() => TemporaryFileSystem.File.Exists(GitCallsPath) ? TemporaryFileSystem.File.ReadAllText(GitCallsPath).Split('\n', StringSplitOptions.RemoveEmptyEntries) : [];
        private (int Exit, string Text, string Error) Run(string executable, string[] args, Dictionary<string, string>? environment = null)
        {
            var start = new ProcessStartInfo(executable) { WorkingDirectory = Root, RedirectStandardOutput = true, RedirectStandardError = true };
            foreach (var arg in args) start.ArgumentList.Add(arg);
            foreach (var pair in environment ?? []) start.Environment[pair.Key] = pair.Value;
            using var process = Process.Start(start)!;
            var stdout = process.StandardOutput.ReadToEndAsync(); var stderr = process.StandardError.ReadToEndAsync();
            Assert.True(process.WaitForExit(30_000), "process exceeded fixture timeout");
            var error = stderr.GetAwaiter().GetResult();
            return (process.ExitCode, stdout.GetAwaiter().GetResult() + error, error);
        }
        public void Dispose() => TemporaryFileSystem.Directory.Delete(scratch, recursive: true);
    }
}
