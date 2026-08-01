using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    private const string ShepherdScriptPath = "Meta/StrataLint/scripts/pr-shepherd.sh";
    private const string CommitSubject =
        "recompute derivations after dev advance (auto, pr-shepherd)";

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

    private static string DryRunWorktreeName(string log)
    {
        const string marker = "ensure worktree path=";
        var start = log.IndexOf(marker, StringComparison.Ordinal);
        Assert.True(start >= 0, log);
        var path = log[(start + marker.Length)..].Split('\n', 2)[0];
        return Path.GetFileName(path);
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
        private readonly string headBranch;
        private readonly bool pauseWorktreeCreation;
        private readonly bool delayFirstLockOwnerRead;
        private readonly bool conflicting;
        private readonly bool ledgerConflict;
        private readonly bool staleBaseRefOid;
        private readonly bool moveHeadDuringFetch;
        private readonly bool moveBaseDuringFetch;
        private int devAdvance;

        internal ShepherdFixture(
            bool sourceConflict = false,
            string failingTarget = "",
            bool moveHeadBeforePush = false,
            bool failMergeWithoutConflict = false,
            bool devDeletesDerived = false,
            string headBranch = "feature",
            bool pauseWorktreeCreation = false,
            bool delayFirstLockOwnerRead = false,
            bool conflicting = false,
            bool ledgerConflict = false,
            bool staleBaseRefOid = false,
            bool moveHeadDuringFetch = false,
            bool moveBaseDuringFetch = false)
        {
            this.failingTarget = failingTarget;
            this.moveHeadBeforePush = moveHeadBeforePush;
            this.failMergeWithoutConflict = failMergeWithoutConflict;
            this.headBranch = headBranch;
            this.pauseWorktreeCreation = pauseWorktreeCreation;
            this.delayFirstLockOwnerRead = delayFirstLockOwnerRead;
            this.conflicting = conflicting;
            this.ledgerConflict = ledgerConflict;
            this.staleBaseRefOid = staleBaseRefOid;
            this.moveHeadDuringFetch = moveHeadDuringFetch;
            this.moveBaseDuringFetch = moveBaseDuringFetch;
            origin = Path.Combine(temporary.Path, "origin.git");
            repository = Path.Combine(temporary.Path, "repository");
            seed = Path.Combine(temporary.Path, "seed");
            bin = Path.Combine(temporary.Path, "bin");
            log = Path.Combine(temporary.Path, "shepherd.log");
            calls = Path.Combine(temporary.Path, "mutation-calls");
            CacheRoot = Path.Combine(temporary.Path, "cache");
            StateDirectory = Path.Combine(temporary.Path, "state");
            Directory.CreateDirectory(bin);

            Git(temporary.Path, "init", "--bare", origin);
            Git(temporary.Path, "init", seed);
            Git(seed, "config", "user.name", "Fixture");
            Git(seed, "config", "user.email", "fixture@example.invalid");
            Write(seed, "Blueprint/input.scribe.cs", "base input\n");
            Write(seed, "Generated/artifact.md", "base artifact\n");
            Write(seed, "Generated/dev-choice.md", "base choice\n");
            Write(seed, "Generated/echo-residual-summary.md", "base echo\n");
            Write(seed, FrozenLedgerChangeClassifier.LedgerPath, "{\"event\":\"base\"}\n");
            Write(seed, "shared.txt", "base shared\n");
            Git(seed, "add", ".");
            Git(seed, "commit", "-m", "base");
            InitialBaseHead = GitOutput(seed, "rev-parse", "HEAD");
            Git(seed, "branch", "-M", "dev");
            Git(seed, "remote", "add", "origin", origin);
            Git(seed, "push", "-u", "origin", "dev");
            Git(temporary.Path, "--git-dir", origin, "symbolic-ref", "HEAD", "refs/heads/dev");

            Git(seed, "checkout", "-b", headBranch);
            Write(seed, "Blueprint/input.scribe.cs", "feature input\n");
            Write(seed, "Generated/artifact.md", "feature artifact\n");
            Write(seed, "Generated/dev-choice.md", "feature choice\n");
            if (sourceConflict) Write(seed, "shared.txt", "feature shared\n");
            if (ledgerConflict)
                Write(
                    seed,
                    FrozenLedgerChangeClassifier.LedgerPath,
                    "{\"event\":\"base\"}\n{\"event\":\"feature-freeze\"}\n");
            Git(seed, "add", ".");
            Git(seed, "commit", "-m", "feature content");
            OriginalHead = GitOutput(seed, "rev-parse", "HEAD");
            Git(seed, "push", "-u", "origin", headBranch);

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
            if (ledgerConflict)
                Write(
                    seed,
                    FrozenLedgerChangeClassifier.LedgerPath,
                    "{\"event\":\"base\"}\n{\"event\":\"dev-freeze\"}\n");
            Git(seed, "add", "-A");
            Git(seed, "commit", "-m", "advance dev");
            BaseHead = GitOutput(seed, "rev-parse", "HEAD");
            Git(seed, "push", "origin", "dev");

            Git(seed, "checkout", "-b", "dev-moved");
            Write(seed, "dev-moved.txt", "dev moved during fetch\n");
            Git(seed, "add", ".");
            Git(seed, "commit", "-m", "move dev during fetch");
            MovedBaseHead = GitOutput(seed, "rev-parse", "HEAD");
            Git(seed, "push", "origin", "dev-moved");
            Git(seed, "checkout", "dev");

            Git(temporary.Path, "clone", origin, repository);
            InstallStubs();
        }

        internal string OriginalHead { get; }

        internal string AttackerHead { get; }

        internal string InitialBaseHead { get; }

        internal string BaseHead { get; private set; }

        internal string MovedBaseHead { get; }

        internal string GithubBaseRefOid => staleBaseRefOid ? InitialBaseHead : BaseHead;

        internal string CacheWorktree =>
            Directory.Exists(CacheRoot)
                ? Directory.GetDirectories(CacheRoot, "wt-*").SingleOrDefault()
                    ?? Path.Combine(CacheRoot, "wt-missing")
                : Path.Combine(CacheRoot, "wt-missing");

        internal string CacheRoot { get; }

        internal string StateDirectory { get; }

        internal ShepherdResult Run(
            bool dryRun = false,
            bool expiryFingerprint = true,
            bool duplicatePrRow = false,
            bool splitFingerprintAcrossJobs = false)
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
                $"PR_SHEPHERD_STATE={StateDirectory}",
                $"PR_SHEPHERD_CACHE={CacheRoot}",
                $"PR_TEST_ORIGIN={origin}",
                $"PR_TEST_HEAD={headBranch}",
                $"PR_TEST_BASE_OID={GithubBaseRefOid}",
                $"PR_TEST_CALLS={calls}",
                $"PR_TEST_EXPIRY={(expiryFingerprint ? "1" : "0")}",
                $"PR_TEST_SPLIT={(splitFingerprintAcrossJobs ? "1" : "0")}",
                $"PR_TEST_DUPLICATE={(duplicatePrRow ? "1" : "0")}",
                $"PR_TEST_FAIL_TARGET={failingTarget}",
                $"PR_TEST_MOVE_HEAD={(moveHeadBeforePush ? "1" : "0")}",
                $"PR_TEST_FAIL_MERGE={(failMergeWithoutConflict ? "1" : "0")}",
                $"PR_TEST_PAUSE_WORKTREE={(pauseWorktreeCreation ? "1" : "0")}",
                $"PR_TEST_DELAY_LOCK_READ={(delayFirstLockOwnerRead ? "1" : "0")}",
                $"PR_TEST_CONFLICTING={(conflicting ? "1" : "0")}",
                $"PR_TEST_MOVE_HEAD_DURING_FETCH={(moveHeadDuringFetch ? "1" : "0")}",
                $"PR_TEST_MOVE_BASE_DURING_FETCH={(moveBaseDuringFetch ? "1" : "0")}",
                $"PR_TEST_MOVED_BASE={MovedBaseHead}",
                $"PR_TEST_LOCK_READ_MARKER={Path.Combine(temporary.Path, "lock-read-marker")}",
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

        internal ShepherdResult RunWatch(bool noChecks = false)
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
                $"PR_SHEPHERD_STATE={StateDirectory}",
                $"PR_SHEPHERD_CACHE={CacheRoot}",
                $"PR_TEST_ORIGIN={origin}",
                $"PR_TEST_HEAD={headBranch}",
                $"PR_TEST_BASE_OID={GithubBaseRefOid}",
                $"PR_TEST_CALLS={calls}",
                $"PR_TEST_WATCH_STATE={Path.Combine(temporary.Path, "watch-state")}",
                "PR_TEST_EXPIRY=1",
                "PR_TEST_SPLIT=0",
                "PR_TEST_DUPLICATE=0",
                "PR_TEST_FAIL_TARGET=",
                "PR_TEST_MOVE_HEAD=0",
                "PR_TEST_FAIL_MERGE=0",
                "PR_TEST_PAUSE_WORKTREE=0",
                "PR_TEST_DELAY_LOCK_READ=0",
                $"PR_TEST_LOCK_READ_MARKER={Path.Combine(temporary.Path, "lock-read-marker")}",
                "PR_TEST_WATCH=1",
                $"PR_TEST_NO_CHECKS={(noChecks ? "1" : "0")}",
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

        internal ShepherdResult RunOpenDryRun()
        {
            var script = Path.Combine(FindRepositoryRoot(), ShepherdScriptPath);
            var home = Path.Combine(temporary.Path, "home");
            Directory.CreateDirectory(home);
            var result = BoundedProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                    $"HOME={home}",
                    "PR_SHEPHERD_REPO=the-omega-institute/trureturing",
                    $"PR_SHEPHERD_LOG={log}",
                    $"PR_TEST_CALLS={calls}",
                    "SHEPHERD_DRYRUN=1",
                    "/bin/bash",
                    script,
                    "open",
                    headBranch,
                    "fixture title",
                ],
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

        internal void HoldBranchLock(string worktreeName) =>
            WriteBranchLock(worktreeName, Environment.ProcessId);

        internal void CreateStaleBranchLock(string worktreeName) =>
            WriteBranchLock(worktreeName, 999_999_999);

        private void WriteBranchLock(string worktreeName, int owner)
        {
            var lockDirectory = Path.Combine(CacheRoot, $"lock-{worktreeName[3..]}");
            Directory.CreateDirectory(lockDirectory);
            File.WriteAllText(
                Path.Combine(lockDirectory, "pid"),
                owner.ToString(System.Globalization.CultureInfo.InvariantCulture));
        }

        internal string[] MutationCalls() =>
            File.Exists(calls) ? File.ReadAllLines(calls) : [];

        internal void ClearMutationCalls() => File.Delete(calls);

        internal string RemoteHead() =>
            GitOutput(temporary.Path, "--git-dir", origin, "rev-parse", $"refs/heads/{headBranch}");

        internal bool IsAncestor(string ancestor, string descendant) =>
            GitResult(repository, "merge-base", "--is-ancestor", ancestor, descendant).ExitCode == 0;

        internal string ShowRemote(string path) =>
            GitResult(
                temporary.Path,
                "--git-dir",
                origin,
                "show",
                $"refs/heads/{headBranch}:{path}").Output;

        internal bool RemoteContains(string path) =>
            GitResult(
                temporary.Path,
                "--git-dir",
                origin,
                "cat-file",
                "-e",
                $"refs/heads/{headBranch}:{path}").ExitCode == 0;

        internal int CountCommitsWithSubject(string subject, string? revision = null) =>
            GitOutput(
                    temporary.Path,
                    "--git-dir",
                    origin,
                    "log",
                    "--format=%s",
                    revision ?? $"refs/heads/{headBranch}")
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
                  head="$(git --git-dir "$PR_TEST_ORIGIN" rev-parse "refs/heads/$PR_TEST_HEAD")"
                  base="$PR_TEST_BASE_OID"
                  if [[ "${PR_TEST_NO_CHECKS:-0}" == 1 ]]; then
                    row="1	MERGEABLE	BLOCKED	${PR_TEST_HEAD}	${head}	${base}	0	-	-"
                  elif [[ "${PR_TEST_CONFLICTING:-0}" == 1 ]]; then
                    row="1	CONFLICTING	DIRTY	${PR_TEST_HEAD}	${head}	${base}	1	FAILURE	https://github.com/fixture/repository/actions/runs/123/job/456"
                  else
                    row="1	MERGEABLE	BEHIND	${PR_TEST_HEAD}	${head}	${base}	1	FAILURE	https://github.com/fixture/repository/actions/runs/123/job/456"
                  fi
                  printf '%b\n' "$row"
                  [[ "$PR_TEST_DUPLICATE" != 1 ]] || printf '%b\n' "$row"
                  exit 0
                fi
                if [[ "${1:-}" == run && "${2:-}" == view ]]; then
                  if [[ "$PR_TEST_SPLIT" == 1 && " $* " != *" --job 456 "* ]]; then
                    printf '%s\n' \
                      'DIGEST_STATUS_INVALID stale Meta/StrataLint/Generated/scribe-emissions.v1.json' \
                      'ECHO_VERIFY_INFRASTRUCTURE residual derivation failed'
                    exit 0
                  fi
                  [[ " $* " == *" --job 456 "* ]] || exit 98
                  if [[ "$PR_TEST_SPLIT" == 1 ]]; then
                    printf '%s\n' 'DIGEST_STATUS_INVALID stale Meta/StrataLint/Generated/scribe-emissions.v1.json'
                    exit 0
                  fi
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
                printf 'gh:%s\n' "$*" >> "$PR_TEST_CALLS"
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
                  [[ "$PR_TEST_PAUSE_WORKTREE" != 1 ]] || sleep 2
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
                if [[ "$*" == *"ledger-append --candidate-lean-report"* ]]; then
                  printf 'ledger-append\n' >> "$PR_TEST_CALLS"
                  exit 0
                fi
                [[ "$*" == *"echo-verify --emit --base origin/dev"* ]] || exit 96
                printf 'echo-verify\n' >> "$PR_TEST_CALLS"
                printf '%s\n' '<!-- echo-residual-summary:v3 residual=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa -->' '# Echo Residual Summary'
                """);
            WriteExecutable(
                "git",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ " $* " == *" fetch --no-tags "* ]]; then
                  if [[ "$PR_TEST_MOVE_HEAD_DURING_FETCH" == 1 ]]; then
                    attacker="$(/usr/bin/git --git-dir "$PR_TEST_ORIGIN" rev-parse refs/heads/attacker)"
                    /usr/bin/git --git-dir "$PR_TEST_ORIGIN" update-ref \
                      "refs/heads/$PR_TEST_HEAD" "$attacker"
                  fi
                  if [[ "$PR_TEST_MOVE_BASE_DURING_FETCH" == 1 ]]; then
                    /usr/bin/git --git-dir "$PR_TEST_ORIGIN" update-ref \
                      refs/heads/dev "$PR_TEST_MOVED_BASE"
                  fi
                fi
                if [[ "$PR_TEST_FAIL_MERGE" == 1 && " $* " == *" merge --no-commit "* ]]; then
                  exit 97
                fi
                if [[ "${PR_TEST_CONFLICTING:-0}" == 1 && " $* " == *" merge --no-commit "* ]]; then
                  printf 'local-merge\n' >> "$PR_TEST_CALLS"
                fi
                if [[ " $* " == *" push "* ]]; then
                  push_call=push
                  for argument in "$@"; do
                    case "$argument" in
                      -f|--force|--force=*|--force-with-lease*|--force-if-includes|+*)
                        push_call=force-push
                        ;;
                    esac
                  done
                  printf '%s\n' "$push_call" >> "$PR_TEST_CALLS"
                fi
                exec /usr/bin/git "$@"
                """);
            WriteExecutable(
                "cat",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "${PR_TEST_DELAY_LOCK_READ:-0}" == 1 && "${1:-}" == */lock-*/pid ]]; then
                  value="$(/bin/cat "$1")"
                  if mkdir "$PR_TEST_LOCK_READ_MARKER" 2>/dev/null; then sleep 1; fi
                  printf '%s' "$value"
                  exit 0
                fi
                exec /bin/cat "$@"
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
