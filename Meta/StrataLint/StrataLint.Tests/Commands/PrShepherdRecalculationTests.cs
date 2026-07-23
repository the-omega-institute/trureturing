using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class PrShepherdRecalculationTests
{
    private const string ShepherdScriptPath = "Meta/StrataLint/scripts/pr-shepherd.sh";
    private const string CommitSubject =
        "recompute derivations after dev advance (auto, pr-shepherd)";

    [Fact]
    public void DryRunPrintsExpiredDerivationPlanWithoutMutatingGitOrGithub()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run(dryRun: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.False(Directory.Exists(fixture.CacheWorktree));
        Assert.Empty(fixture.MutationCalls());
        AssertInOrder(
            result.Log,
            "DRYRUN #1 BEHIND stale derivations -> ensure worktree",
            "DRYRUN #1 fetch origin/dev and origin/feature; verify observed OIDs",
            "DRYRUN #1 checkout feature; merge origin/dev (derived conflicts take dev)",
            "DRYRUN #1 run make lean-report",
            "DRYRUN #1 run make emit",
            "DRYRUN #1 run make ingest BASE=origin/dev",
            "DRYRUN #1 run echo-verify --emit --base origin/dev (atomic install)",
            "DRYRUN #1 run make emit-check BASE=origin/dev",
            $"DRYRUN #1 commit: {CommitSubject}",
            "DRYRUN #1 push HEAD:refs/heads/feature (non-force)");
    }

    [Fact]
    public void BehindWithoutExpiryFingerprintRetainsExactUpdateBranchBehavior()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run(expiryFingerprint: false);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            ["gh-api:-X PUT repos/the-omega-institute/trureturing/pulls/1/update-branch"],
            fixture.MutationCalls());
        Assert.EndsWith(
            "SWEEP #1 BEHIND -> update-branch(本地身份,checks 会触发)\n",
            result.Log,
            StringComparison.Ordinal);
        Assert.False(Directory.Exists(fixture.CacheWorktree));
    }

    [Fact]
    public void ExpiredAdmissionReusesPersistentWorktreeAndRunsCanonicalChainOncePerSweep()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var first = fixture.Run(duplicatePrRow: true);

        Assert.Equal(0, first.ExitCode);
        var firstHead = fixture.RemoteHead();
        Assert.NotEqual(fixture.OriginalHead, firstHead);
        Assert.True(fixture.IsAncestor(fixture.BaseHead, firstHead));
        Assert.Equal("derived artifact\n", fixture.ShowRemote("Generated/artifact.md"));
        Assert.Equal(
            ["worktree", "lean-report", "emit", "ingest", "echo-verify", "emit-check", "push"],
            fixture.MutationCalls());
        Assert.Equal(1, fixture.CountCommitsWithSubject(CommitSubject));
        Assert.True(Directory.Exists(fixture.CacheWorktree));

        fixture.AdvanceDev();
        fixture.ClearMutationCalls();
        var second = fixture.Run();

        Assert.Equal(0, second.ExitCode);
        var secondHead = fixture.RemoteHead();
        Assert.NotEqual(firstHead, secondHead);
        Assert.True(fixture.IsAncestor(fixture.BaseHead, secondHead));
        Assert.Equal(
            ["lean-report", "emit", "ingest", "echo-verify", "emit-check", "push"],
            fixture.MutationCalls());
        Assert.Equal(2, fixture.CountCommitsWithSubject(CommitSubject));
    }

    [Fact]
    public void SourceConflictKeepsExistingConflictingAlertAndDoesNotPush()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(sourceConflict: true);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.DoesNotContain("push", fixture.MutationCalls());
        Assert.Contains(
            "ALERT #1 CONFLICTING head=feature 需语义合并(派 shepherd lane,本器不代解)",
            result.Log,
            StringComparison.Ordinal);
    }

    [Fact]
    public void DerivedConflictTakesDevSideBeforeReemission()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.NotEqual(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal("dev choice\n", fixture.ShowRemote("Generated/dev-choice.md"));
        Assert.Contains("push", fixture.MutationCalls());
    }

    [Fact]
    public void DerivedConflictAcceptsDeletionFromDevBeforeReemission()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(devDeletesDerived: true);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.NotEqual(fixture.OriginalHead, fixture.RemoteHead());
        Assert.False(fixture.RemoteContains("Generated/dev-choice.md"));
        Assert.Contains("push", fixture.MutationCalls());
    }

    [Fact]
    public void EmitCheckFailureLeavesRemoteHeadUntouched()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingTarget: "emit-check");

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal(
            ["worktree", "lean-report", "emit", "ingest", "echo-verify", "emit-check"],
            fixture.MutationCalls());
        Assert.Contains("emit-check 失败,不 push", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void NonConflictMergeFailureStopsBeforeDerivationAndPush()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failMergeWithoutConflict: true);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal(["worktree"], fixture.MutationCalls());
        Assert.Contains("merge origin/dev 失败,不 push", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void NonFastForwardPushIsAbandonedWithoutOverwritingConcurrentHead()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(moveHeadBeforePush: true);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.AttackerHead, fixture.RemoteHead());
        Assert.Contains("push 非 FF 被拒,放弃本轮(下轮重试)", result.Log, StringComparison.Ordinal);
        Assert.Equal(0, fixture.CountCommitsWithSubject(CommitSubject, "refs/heads/feature"));
    }

    [Fact]
    public void ScriptClassifierUsesLatestFailedAdmissionMachineFieldsAndAllExpiryTokens()
    {
        var root = FindRepositoryRoot();
        var script = File.ReadAllText(Path.Combine(root, ShepherdScriptPath));

        Assert.Contains("Content-addressed dev baseline admission", script, StringComparison.Ordinal);
        Assert.Contains("completedAt", script, StringComparison.Ordinal);
        Assert.Contains("conclusion", script, StringComparison.Ordinal);
        Assert.Contains("detailsUrl", script, StringComparison.Ordinal);
        Assert.Contains("DIGEST_STATUS_INVALID", script, StringComparison.Ordinal);
        Assert.Contains("scribe-emissions", script, StringComparison.Ordinal);
        Assert.Contains("ECHO_VERIFY_INFRASTRUCTURE", script, StringComparison.Ordinal);
        Assert.Contains("residual", script, StringComparison.Ordinal);
        Assert.Contains("SHEPHERD_DRYRUN", script, StringComparison.Ordinal);
    }

    [Fact]
    public void WatchRestartsCycleBudgetWhileAnArmedPullRequestRemainsOpen()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.RunWatch();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            2,
            result.Log.Split(
                "DRYRUN #1 BEHIND stale derivations -> ensure worktree",
                StringSplitOptions.None).Length - 1);
        Assert.Contains(
            "WATCH renew(1 轮耗尽,仍有 open 且 auto-merge armed PR,重启计数)",
            result.Log,
            StringComparison.Ordinal);
        Assert.EndsWith(
            "WATCH end(1 轮耗尽,无 open auto-merge armed PR)\n",
            result.Log,
            StringComparison.Ordinal);
    }

    private static void AssertInOrder(string text, params string[] fragments)
    {
        var cursor = 0;
        foreach (var fragment in fragments)
        {
            var index = text.IndexOf(fragment, cursor, StringComparison.Ordinal);
            Assert.True(index >= cursor, $"missing ordered fragment: {fragment}\n{text}");
            cursor = index + fragment.Length;
        }
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

    private sealed class ShepherdFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string origin;
        private readonly string repository;
        private readonly string seed;
        private readonly string bin;
        private readonly string log;
        private readonly string calls;
        private readonly string failingTarget;
        private readonly bool moveHeadBeforePush;
        private readonly bool failMergeWithoutConflict;
        private int devAdvance;

        internal ShepherdFixture(
            bool sourceConflict = false,
            string failingTarget = "",
            bool moveHeadBeforePush = false,
            bool failMergeWithoutConflict = false,
            bool devDeletesDerived = false)
        {
            this.failingTarget = failingTarget;
            this.moveHeadBeforePush = moveHeadBeforePush;
            this.failMergeWithoutConflict = failMergeWithoutConflict;
            origin = Path.Combine(temporary.Path, "origin.git");
            repository = Path.Combine(temporary.Path, "repository");
            seed = Path.Combine(temporary.Path, "seed");
            bin = Path.Combine(temporary.Path, "bin");
            log = Path.Combine(temporary.Path, "shepherd.log");
            calls = Path.Combine(temporary.Path, "mutation-calls");
            CacheWorktree = Path.Combine(temporary.Path, "cache", "wt-feature");
            Directory.CreateDirectory(bin);

            Git(temporary.Path, "init", "--bare", origin);
            Git(temporary.Path, "init", seed);
            Git(seed, "config", "user.name", "Fixture");
            Git(seed, "config", "user.email", "fixture@example.invalid");
            Write(seed, "Blueprint/input.scribe.cs", "base input\n");
            Write(seed, "Generated/artifact.md", "base artifact\n");
            Write(seed, "Generated/dev-choice.md", "base choice\n");
            Write(seed, "Generated/echo-residual-summary.md", "base echo\n");
            Write(seed, "shared.txt", "base shared\n");
            Git(seed, "add", ".");
            Git(seed, "commit", "-m", "base");
            Git(seed, "branch", "-M", "dev");
            Git(seed, "remote", "add", "origin", origin);
            Git(seed, "push", "-u", "origin", "dev");
            Git(temporary.Path, "--git-dir", origin, "symbolic-ref", "HEAD", "refs/heads/dev");

            Git(seed, "checkout", "-b", "feature");
            Write(seed, "Blueprint/input.scribe.cs", "feature input\n");
            Write(seed, "Generated/artifact.md", "feature artifact\n");
            Write(seed, "Generated/dev-choice.md", "feature choice\n");
            if (sourceConflict) Write(seed, "shared.txt", "feature shared\n");
            Git(seed, "add", ".");
            Git(seed, "commit", "-m", "feature content");
            OriginalHead = GitOutput(seed, "rev-parse", "HEAD");
            Git(seed, "push", "-u", "origin", "feature");

            Git(seed, "checkout", "-b", "attacker");
            Write(seed, "attacker.txt", "concurrent head\n");
            Git(seed, "add", "attacker.txt");
            Git(seed, "commit", "-m", "concurrent feature update");
            AttackerHead = GitOutput(seed, "rev-parse", "HEAD");
            Git(seed, "push", "origin", "attacker");

            Git(seed, "checkout", "dev");
            Write(seed, "Generated/artifact.md", "dev artifact\n");
            if (devDeletesDerived)
                File.Delete(Path.Combine(seed, "Generated", "dev-choice.md"));
            else
                Write(seed, "Generated/dev-choice.md", "dev choice\n");
            Write(seed, sourceConflict ? "shared.txt" : "dev-input.txt", "advanced dev\n");
            Git(seed, "add", "-A");
            Git(seed, "commit", "-m", "advance dev");
            BaseHead = GitOutput(seed, "rev-parse", "HEAD");
            Git(seed, "push", "origin", "dev");

            Git(temporary.Path, "clone", origin, repository);
            InstallStubs();
        }

        internal string OriginalHead { get; }

        internal string AttackerHead { get; }

        internal string BaseHead { get; private set; }

        internal string CacheWorktree { get; }

        internal ShepherdResult Run(
            bool dryRun = false,
            bool expiryFingerprint = true,
            bool duplicatePrRow = false)
        {
            var script = Path.Combine(FindRepositoryRoot(), ShepherdScriptPath);
            var home = Path.Combine(temporary.Path, "home");
            Directory.CreateDirectory(home);
            var arguments = new List<string>
            {
                $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                $"HOME={home}",
                $"PR_SHEPHERD_ROOT={repository}",
                "PR_SHEPHERD_REMOTE=origin",
                "PR_SHEPHERD_REPO=the-omega-institute/trureturing",
                $"PR_SHEPHERD_LOG={log}",
                $"PR_SHEPHERD_STATE={Path.Combine(temporary.Path, "state")}",
                $"PR_SHEPHERD_CACHE={Path.Combine(temporary.Path, "cache")}",
                $"PR_TEST_ORIGIN={origin}",
                $"PR_TEST_CALLS={calls}",
                $"PR_TEST_EXPIRY={(expiryFingerprint ? "1" : "0")}",
                $"PR_TEST_DUPLICATE={(duplicatePrRow ? "1" : "0")}",
                $"PR_TEST_FAIL_TARGET={failingTarget}",
                $"PR_TEST_MOVE_HEAD={(moveHeadBeforePush ? "1" : "0")}",
                $"PR_TEST_FAIL_MERGE={(failMergeWithoutConflict ? "1" : "0")}",
                $"SHEPHERD_DRYRUN={(dryRun ? "1" : "0")}",
                "GH_TOKEN=must-not-reach-candidate-producers",
                "/bin/bash",
                script,
                "sweep",
            };
            var result = BoundedProcessRunner.Run(
                "/usr/bin/env",
                arguments,
                repository,
                TimeSpan.FromSeconds(30),
                256 * 1024);
            return new ShepherdResult(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError),
                File.Exists(log) ? File.ReadAllText(log) : string.Empty);
        }

        internal ShepherdResult RunWatch()
        {
            var script = Path.Combine(FindRepositoryRoot(), ShepherdScriptPath);
            var home = Path.Combine(temporary.Path, "home");
            Directory.CreateDirectory(home);
            var arguments = new List<string>
            {
                $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                $"HOME={home}",
                $"PR_SHEPHERD_ROOT={repository}",
                "PR_SHEPHERD_REMOTE=origin",
                "PR_SHEPHERD_REPO=the-omega-institute/trureturing",
                $"PR_SHEPHERD_LOG={log}",
                $"PR_SHEPHERD_PID={Path.Combine(temporary.Path, "shepherd.pid")}",
                $"PR_SHEPHERD_STATE={Path.Combine(temporary.Path, "state")}",
                $"PR_SHEPHERD_CACHE={Path.Combine(temporary.Path, "cache")}",
                $"PR_TEST_ORIGIN={origin}",
                $"PR_TEST_CALLS={calls}",
                $"PR_TEST_WATCH_STATE={Path.Combine(temporary.Path, "watch-state")}",
                "PR_TEST_EXPIRY=1",
                "PR_TEST_DUPLICATE=0",
                "PR_TEST_FAIL_TARGET=",
                "PR_TEST_MOVE_HEAD=0",
                "PR_TEST_FAIL_MERGE=0",
                "PR_TEST_WATCH=1",
                "SHEPHERD_DRYRUN=1",
                "/bin/bash",
                script,
                "watch",
                "0",
                "1",
            };
            var result = BoundedProcessRunner.Run(
                "/usr/bin/env",
                arguments,
                repository,
                TimeSpan.FromSeconds(30),
                256 * 1024);
            return new ShepherdResult(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError),
                File.Exists(log) ? File.ReadAllText(log) : string.Empty);
        }

        internal void AdvanceDev()
        {
            devAdvance++;
            Git(seed, "checkout", "dev");
            Write(seed, $"dev-advance-{devAdvance}.txt", $"advance {devAdvance}\n");
            Git(seed, "add", ".");
            Git(seed, "commit", "-m", $"advance dev {devAdvance}");
            BaseHead = GitOutput(seed, "rev-parse", "HEAD");
            Git(seed, "push", "origin", "dev");
        }

        internal string[] MutationCalls() =>
            File.Exists(calls) ? File.ReadAllLines(calls) : [];

        internal void ClearMutationCalls() => File.Delete(calls);

        internal string RemoteHead() =>
            GitOutput(temporary.Path, "--git-dir", origin, "rev-parse", "refs/heads/feature");

        internal bool IsAncestor(string ancestor, string descendant) =>
            GitResult(repository, "merge-base", "--is-ancestor", ancestor, descendant).ExitCode == 0;

        internal string ShowRemote(string path) =>
            GitResult(temporary.Path, "--git-dir", origin, "show", $"refs/heads/feature:{path}").Output;

        internal bool RemoteContains(string path) =>
            GitResult(
                temporary.Path,
                "--git-dir",
                origin,
                "cat-file",
                "-e",
                $"refs/heads/feature:{path}").ExitCode == 0;

        internal int CountCommitsWithSubject(string subject, string revision = "refs/heads/feature") =>
            GitOutput(temporary.Path, "--git-dir", origin, "log", "--format=%s", revision)
                .Split('\n', StringSplitOptions.RemoveEmptyEntries)
                .Count(line => string.Equals(line, subject, StringComparison.Ordinal));

        public void Dispose() => temporary.Dispose();

        private void InstallStubs()
        {
            WriteExecutable(
                "gh",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "${1:-}" == pr && "${2:-}" == list ]]; then
                  [[ " $* " == *" --limit 1000 "* ]] || exit 97
                  if [[ "${PR_TEST_WATCH:-0}" == 1 && " $* " == *" --json autoMergeRequest "* ]]; then
                    count=0
                    [[ ! -f "$PR_TEST_WATCH_STATE" ]] || count="$(cat "$PR_TEST_WATCH_STATE")"
                    count=$((count + 1))
                    printf '%s' "$count" > "$PR_TEST_WATCH_STATE"
                    if [[ "$count" == 1 ]]; then printf '1\n'; else printf '0\n'; fi
                    exit 0
                  fi
                  head="$(git --git-dir "$PR_TEST_ORIGIN" rev-parse refs/heads/feature)"
                  base="$(git --git-dir "$PR_TEST_ORIGIN" rev-parse refs/heads/dev)"
                  row="1	MERGEABLE	BEHIND	feature	${head}	${base}	1	FAILURE	https://github.com/fixture/repository/actions/runs/123/jobs/456"
                  printf '%b\n' "$row"
                  [[ "$PR_TEST_DUPLICATE" != 1 ]] || printf '%b\n' "$row"
                  exit 0
                fi
                if [[ "${1:-}" == run && "${2:-}" == view ]]; then
                  if [[ "$PR_TEST_EXPIRY" == 1 ]]; then
                    printf '%s\n' \
                      'DIGEST_STATUS_INVALID stale Meta/StrataLint/Generated/scribe-emissions.v1.json' \
                      'ECHO_VERIFY_INFRASTRUCTURE residual derivation failed'
                  else
                    printf '%s\n' 'SL-001 unrelated admission failure'
                  fi
                  exit 0
                fi
                if [[ "${1:-}" == api ]]; then
                  printf 'gh-api:%s\n' "${*:2}" >> "$PR_TEST_CALLS"
                  exit 0
                fi
                exit 95
                """);
            WriteExecutable(
                "make",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "${1:-}" != -C || "${4:-}" != worktree ]]; then
                  [[ -z "${GH_TOKEN+x}" ]] || exit 91
                  [[ -z "${GITHUB_TOKEN+x}" ]] || exit 92
                fi
                root="$PWD"
                if [[ "${1:-}" == -C ]]; then root="$2"; shift 2; fi
                [[ "${1:-}" != --no-print-directory ]] || shift
                target="${1:-}"
                if [[ "$target" == worktree ]]; then
                  name=''; path=''; base=''
                  for argument in "$@"; do
                    case "$argument" in
                      NAME=*) name="${argument#NAME=}" ;;
                      PATH=*) path="${argument#PATH=}" ;;
                      BASE=*) base="${argument#BASE=}" ;;
                    esac
                  done
                  git -C "$root" worktree add -b "harness/$name" "$path" "$base" >/dev/null
                  printf 'worktree\n' >> "$PR_TEST_CALLS"
                  exit 0
                fi
                printf '%s\n' "$target" >> "$PR_TEST_CALLS"
                [[ "$target" != "$PR_TEST_FAIL_TARGET" ]] || exit 93
                case "$target" in
                  lean-report) mkdir -p "$root/.lake/build/stratalint" ;;
                  emit)
                    mkdir -p "$root/Generated"
                    printf 'derived artifact\n' > "$root/Generated/artifact.md"
                    ;;
                  ingest) ;;
                  emit-check)
                    if [[ "$PR_TEST_MOVE_HEAD" == 1 ]]; then
                      attacker="$(git --git-dir "$PR_TEST_ORIGIN" rev-parse refs/heads/attacker)"
                      git --git-dir "$PR_TEST_ORIGIN" update-ref refs/heads/feature "$attacker"
                    fi
                    ;;
                  *) exit 94 ;;
                esac
                """);
            WriteExecutable(
                "dotnet",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                [[ -z "${GH_TOKEN+x}" ]] || exit 91
                [[ -z "${GITHUB_TOKEN+x}" ]] || exit 92
                [[ "$*" == *"echo-verify --emit --base origin/dev"* ]] || exit 96
                printf 'echo-verify\n' >> "$PR_TEST_CALLS"
                printf '%s\n' '<!-- echo-residual-summary:v2 base=git-sha1:1111111111111111111111111111111111111111 -->' '# Echo Residual Summary'
                """);
            WriteExecutable(
                "git",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "$PR_TEST_FAIL_MERGE" == 1 && " $* " == *" merge --no-commit "* ]]; then
                  exit 97
                fi
                if [[ " $* " == *" push "* ]]; then printf 'push\n' >> "$PR_TEST_CALLS"; fi
                exec /usr/bin/git "$@"
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
                "/usr/bin/git",
                arguments,
                workingDirectory,
                TimeSpan.FromSeconds(15),
                64 * 1024);
            return new CommandResult(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError));
        }
    }

    private sealed record ShepherdResult(int ExitCode, string Output, string Error, string Log);

    private sealed record CommandResult(int ExitCode, string Output, string Error);
}
