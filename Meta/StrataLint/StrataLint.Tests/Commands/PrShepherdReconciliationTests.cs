using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class PrShepherdReconciliationTests
{
    private const string ReconcileScriptPath = "Meta/StrataLint/scripts/pr-reconcile.sh";

    [Fact]
    public void ReconciliationRederivesInCanonicalOrderWithoutCredentialsAndIsIdempotent()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReconciliationFixture();

        var first = fixture.Run();

        Assert.Equal(0, first.ExitCode);
        var reconciledHead = fixture.RemoteHead();
        Assert.NotEqual(fixture.OriginalHead, reconciledHead);
        Assert.True(fixture.IsAncestor(fixture.BaseHead, reconciledHead));
        Assert.Equal("derived artifact\n", fixture.ShowRemote("Generated/artifact.md"));
        Assert.Equal(
            ["lean-report", "emit", "ingest", "echo-residual-summary"],
            fixture.DerivationCalls());
        Assert.Equal(1, fixture.CountCommitsWithSubject("chore(derived): rederive after dev merge"));

        var second = fixture.Run(expectedHead: reconciledHead);

        Assert.Equal(0, second.ExitCode);
        Assert.Equal(reconciledHead, fixture.RemoteHead());
        Assert.Equal(1, fixture.CountCommitsWithSubject("chore(derived): rederive after dev merge"));
    }

    [Fact]
    public void DerivationFailureLeavesTheObservedHeadUntouched()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReconciliationFixture(failingTarget: "ingest");

        var result = fixture.Run();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal(["lean-report", "emit", "ingest"], fixture.DerivationCalls());
    }

    [Fact]
    public void SemanticMergeConflictRefusesDerivationAndWriteback()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReconciliationFixture(conflictingMerge: true);

        var result = fixture.Run();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("merge conflict", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Empty(fixture.DerivationCalls());
    }

    [Theory]
    [InlineData("head")]
    [InlineData("base")]
    public void ConcurrentRefMovementRefusesWriteback(string movingRef)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReconciliationFixture(movingRef: movingRef);

        var result = fixture.Run();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("changed during reconciliation", result.Error, StringComparison.Ordinal);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
    }

    [Fact]
    public void ProducerWriteOutsideTheCanonicalWhitelistRefusesWriteback()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReconciliationFixture(writeOutsideWhitelist: true);

        var result = fixture.Run();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("outside the derivation whitelist", result.Error, StringComparison.Ordinal);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
    }

    [Fact]
    public void ProducerCannotHideAnOutsideWriteInTheGitIndex()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReconciliationFixture(stageOutsideWhitelist: true);

        var result = fixture.Run();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("outside the derivation whitelist", result.Error, StringComparison.Ordinal);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
    }

    [Fact]
    public void ProducerCannotHideAnOutsideWriteInANewCommit()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReconciliationFixture(commitOutsideWhitelist: true);

        var result = fixture.Run();

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("changed HEAD", result.Error, StringComparison.Ordinal);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
    }

    [Fact]
    public void CrossRepositoryNonContentPrRemainsEligibleForTextMergeFallback()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReconciliationFixture(generatedContent: false, crossRepository: true);

        var result = fixture.Run();

        Assert.Equal(3, result.ExitCode);
        Assert.Empty(fixture.DerivationCalls());
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
    }

    private sealed class ReconciliationFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string origin;
        private readonly string repository;
        private readonly string bin;
        private readonly string calls;
        private readonly string movingRef;
        private readonly string failingTarget;
        private readonly bool writeOutsideWhitelist;
        private readonly bool stageOutsideWhitelist;
        private readonly bool commitOutsideWhitelist;
        private readonly bool crossRepository;

        internal ReconciliationFixture(
            bool conflictingMerge = false,
            string movingRef = "",
            string failingTarget = "",
            bool writeOutsideWhitelist = false,
            bool stageOutsideWhitelist = false,
            bool commitOutsideWhitelist = false,
            bool generatedContent = true,
            bool crossRepository = false)
        {
            this.movingRef = movingRef;
            this.failingTarget = failingTarget;
            this.writeOutsideWhitelist = writeOutsideWhitelist;
            this.stageOutsideWhitelist = stageOutsideWhitelist;
            this.commitOutsideWhitelist = commitOutsideWhitelist;
            this.crossRepository = crossRepository;
            origin = Path.Combine(temporary.Path, "origin.git");
            repository = Path.Combine(temporary.Path, "repository");
            bin = Path.Combine(temporary.Path, "bin");
            calls = Path.Combine(temporary.Path, "derivation-calls");
            var seed = Path.Combine(temporary.Path, "seed");
            Directory.CreateDirectory(bin);

            Git(temporary.Path, "init", "--bare", origin);
            Git(temporary.Path, "init", seed);
            Git(seed, "config", "user.name", "Fixture");
            Git(seed, "config", "user.email", "fixture@example.invalid");
            Write(seed, "Blueprint/input.scribe.cs", "base input\n");
            Write(seed, "Generated/artifact.md", "base artifact\n");
            Write(seed, "Generated/echo-residual-summary.md", "echo summary\n");
            Write(seed, "shared.txt", "base\n");
            Git(seed, "add", ".");
            Git(seed, "commit", "-m", "base");
            Git(seed, "branch", "-M", "dev");
            Git(seed, "remote", "add", "origin", origin);
            Git(seed, "push", "-u", "origin", "dev");
            Git(temporary.Path, "--git-dir", origin, "symbolic-ref", "HEAD", "refs/heads/dev");

            Git(seed, "checkout", "-b", "feature");
            Write(seed, "Blueprint/input.scribe.cs", "feature input\n");
            if (generatedContent) Write(seed, "Generated/artifact.md", "feature artifact\n");
            if (conflictingMerge) Write(seed, "shared.txt", "feature\n");
            Git(seed, "add", ".");
            Git(seed, "commit", "-m", "content change");
            OriginalHead = GitOutput(seed, "rev-parse", "HEAD");
            Git(seed, "push", "-u", "origin", "feature");
            Git(temporary.Path, "--git-dir", origin, "update-ref", "refs/pull/1/head", OriginalHead);

            Git(seed, "checkout", "dev");
            Write(seed, conflictingMerge ? "shared.txt" : "base-input.txt", "advanced dev\n");
            Git(seed, "add", ".");
            Git(seed, "commit", "-m", "advance dev");
            BaseHead = GitOutput(seed, "rev-parse", "HEAD");
            Git(seed, "push", "origin", "dev");
            Git(temporary.Path, "clone", origin, repository);
            InstallStubs();
        }

        internal string OriginalHead { get; }

        internal string BaseHead { get; }

        internal ReconcileResult Run(string? expectedHead = null)
        {
            var script = Path.Combine(FindRepositoryRoot(), ReconcileScriptPath);
            var arguments = new List<string>
            {
                $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                $"PR_SHEPHERD_ROOT={repository}",
                "PR_SHEPHERD_REMOTE=origin",
                "PR_SHEPHERD_REPO=fixture/repository",
                $"PR_SHEPHERD_LOG={Path.Combine(temporary.Path, "shepherd.log")}",
                $"PR_SHEPHERD_STATE={Path.Combine(temporary.Path, "state")}",
                $"PR_TEST_ORIGIN={origin}",
                $"PR_TEST_CALLS={calls}",
                $"PR_TEST_MOVING_REF={movingRef}",
                $"PR_TEST_FAIL_TARGET={failingTarget}",
                $"PR_TEST_WRITE_OUTSIDE={(writeOutsideWhitelist ? "1" : "0")}",
                $"PR_TEST_STAGE_OUTSIDE={(stageOutsideWhitelist ? "1" : "0")}",
                $"PR_TEST_COMMIT_OUTSIDE={(commitOutsideWhitelist ? "1" : "0")}",
                "GH_TOKEN=must-not-reach-producers",
                "/bin/bash",
                script,
                "1",
                "feature",
                expectedHead ?? OriginalHead,
                BaseHead,
                crossRepository ? "true" : "false",
            };
            var result = BoundedProcessRunner.Run(
                "/usr/bin/env",
                arguments,
                repository,
                TimeSpan.FromSeconds(30),
                128 * 1024);
            return new ReconcileResult(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError));
        }

        internal string RemoteHead() =>
            GitOutput(temporary.Path, "--git-dir", origin, "rev-parse", "refs/heads/feature");

        internal bool IsAncestor(string ancestor, string descendant) =>
            GitResult(repository, "merge-base", "--is-ancestor", ancestor, descendant).ExitCode == 0;

        internal string ShowRemote(string path) =>
            GitResult(temporary.Path, "--git-dir", origin, "show", $"refs/heads/feature:{path}").Output;

        internal int CountCommitsWithSubject(string subject) =>
            GitOutput(temporary.Path, "--git-dir", origin, "log", "--format=%s", "refs/heads/feature")
                .Split('\n', StringSplitOptions.RemoveEmptyEntries)
                .Count(line => string.Equals(line, subject, StringComparison.Ordinal));

        internal string[] DerivationCalls() =>
            File.Exists(calls)
                ? File.ReadAllLines(calls)
                : [];

        public void Dispose() => temporary.Dispose();

        private void InstallStubs()
        {
            WriteExecutable(
                "dotnet",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                [[ "$*" == *"artifact-inventory --null"* ]] || exit 90
                printf 'Generated/artifact.md\0Generated/echo-residual-summary.md\0'
                """);
            WriteExecutable(
                "make",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                [[ -z "${GH_TOKEN+x}" ]] || exit 91
                [[ -z "${GITHUB_TOKEN+x}" ]] || exit 92
                [[ "$1" == "-C" ]]
                workspace="$2"
                shift 2
                [[ "${1:-}" == "--no-print-directory" ]] && shift
                target="$1"
                printf '%s\n' "$target" >> "$PR_TEST_CALLS"
                [[ "$target" != "$PR_TEST_FAIL_TARGET" ]] || exit 93
                case "$target" in
                  lean-report|ingest) ;;
                  emit)
                    printf 'derived artifact\n' > "$workspace/Generated/artifact.md"
                    if [[ "$PR_TEST_WRITE_OUTSIDE" == 1 ]]; then
                      printf 'unexpected\n' > "$workspace/outside.txt"
                    fi
                    if [[ "$PR_TEST_STAGE_OUTSIDE" == 1 ]]; then
                      printf 'unexpected\n' > "$workspace/outside.txt"
                      git -C "$workspace" add outside.txt
                    fi
                    if [[ "$PR_TEST_COMMIT_OUTSIDE" == 1 ]]; then
                      printf 'unexpected\n' > "$workspace/outside.txt"
                      git -C "$workspace" add Generated/artifact.md outside.txt
                      git -C "$workspace" \
                        -c user.name=Fixture \
                        -c user.email=fixture@example.invalid \
                        commit -m 'candidate producer commit' >/dev/null
                    fi
                    ;;
                  echo-residual-summary) printf 'echo summary\n' ;;
                  *) exit 94 ;;
                esac
                """);
            WriteExecutable(
                "gh",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "$*" == *"pr view"* ]]; then
                  head="$(git --git-dir "$PR_TEST_ORIGIN" rev-parse refs/heads/feature)"
                  base="$(git --git-dir "$PR_TEST_ORIGIN" rev-parse refs/heads/dev)"
                  [[ "$PR_TEST_MOVING_REF" != head ]] || head=1111111111111111111111111111111111111111
                  [[ "$PR_TEST_MOVING_REF" != base ]] || base=2222222222222222222222222222222222222222
                  printf '%s\t%s\tfeature\tfalse\n' "$head" "$base"
                  exit 0
                fi
                [[ "$*" == *"auth setup-git"* ]] && exit 0
                exit 95
                """);
        }

        private void WriteExecutable(string name, string contents)
        {
            if (OperatingSystem.IsWindows()) return;
            var path = Path.Combine(bin, name);
            File.WriteAllText(path, contents + "\n", new UTF8Encoding(false));
            File.SetUnixFileMode(
                path,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        private static void Write(string root, string relativePath, string contents)
        {
            var path = Path.Combine(root, relativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, contents, new UTF8Encoding(false));
        }

        private static void Git(string workingDirectory, params string[] arguments)
        {
            var result = GitResult(workingDirectory, arguments);
            Assert.True(
                result.ExitCode == 0,
                $"git {string.Join(' ', arguments)} failed ({result.ExitCode}): {result.Error}");
        }

        private static string GitOutput(string workingDirectory, params string[] arguments)
        {
            var result = GitResult(workingDirectory, arguments);
            Assert.True(
                result.ExitCode == 0,
                $"git {string.Join(' ', arguments)} failed ({result.ExitCode}): {result.Error}");
            return result.Output.TrimEnd();
        }

        private static CommandResult GitResult(string workingDirectory, params string[] arguments)
        {
            var result = BoundedProcessRunner.Run(
                "git",
                arguments,
                workingDirectory,
                TimeSpan.FromSeconds(15),
                64 * 1024);
            return new CommandResult(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError));
        }

        private static string FindRepositoryRoot()
        {
            for (var current = new DirectoryInfo(AppContext.BaseDirectory);
                 current is not null;
                 current = current.Parent)
            {
                if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
            }

            throw new DirectoryNotFoundException("Could not locate repository root.");
        }
    }

    private sealed record ReconcileResult(int ExitCode, string Output, string Error);

    private sealed record CommandResult(int ExitCode, string Output, string Error);
}
