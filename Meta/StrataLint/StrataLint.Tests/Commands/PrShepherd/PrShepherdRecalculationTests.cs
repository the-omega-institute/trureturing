using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    private const string ShepherdScriptPath = "Meta/StrataLint/scripts/pr-shepherd.sh";
    private const string ShepherdLeaseScriptPath =
        "Meta/StrataLint/scripts/shepherd/pr-shepherd-lease.sh";
    private const string ShepherdActionsScriptPath =
        "Meta/StrataLint/scripts/shepherd/pr-shepherd-actions.sh";
    private const string ShepherdLedgerScriptPath =
        "Meta/StrataLint/scripts/shepherd/pr-shepherd-ledger.sh";
    private const string ShepherdFixedPointScriptPath =
        "Meta/StrataLint/scripts/shepherd/pr-shepherd-fixed-point.sh";
    private const string ShepherdWatchScriptPath =
        "Meta/StrataLint/scripts/shepherd/pr-shepherd-watch.sh";
    private const string ShepherdWakeScriptPath =
        "Meta/StrataLint/scripts/shepherd/pr-shepherd-wake.sh";
    private const string CommitSubject = "recompute the truth graph";

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

    private static string ReadShepherdScripts()
    {
        var root = FindRepositoryRoot();
        return string.Join(
            '\n',
            File.ReadAllText(Path.Combine(root, ShepherdScriptPath)),
            File.ReadAllText(Path.Combine(root, ShepherdActionsScriptPath)),
            File.ReadAllText(Path.Combine(root, ShepherdLedgerScriptPath)),
            File.ReadAllText(Path.Combine(root, ShepherdFixedPointScriptPath)),
            File.ReadAllText(Path.Combine(root, ShepherdWatchScriptPath)),
            File.ReadAllText(Path.Combine(root, ShepherdWakeScriptPath)),
            File.ReadAllText(Path.Combine(root, ShepherdLeaseScriptPath)));
    }

    private sealed partial class ShepherdFixture : IDisposable
    {
        internal const string GhAppToken = "fixture-gh-app-token";

        private readonly TemporaryDirectory temporary = new();
        private readonly string origin;
        private readonly string repository;
        private readonly string seed;
        private readonly string bin;
        private readonly string log;
        private readonly string calls;
        private readonly string boundedCalls;
        private readonly string hangingPids;
        private string failingTarget;
        private readonly int failingExitCode;
        private readonly int failingPr;
        private readonly string hangingTarget;
        private string failingGhOperation;
        private readonly bool moveHeadBeforePush;
        private readonly bool failMergeWithoutConflict;
        private readonly string headBranch;
        private readonly bool pauseWorktreeCreation;
        private readonly bool delayFirstLockOwnerRead;
        private readonly bool conflicting;
        private readonly bool ledgerConflict;
        private readonly string graphqlRemaining;
        private readonly bool staleBaseRefOid;
        private readonly bool moveHeadDuringFetch;
        private readonly bool moveBaseDuringFetch;
        private readonly int truthGraphDirtyRounds;
        private int devAdvance;
        private int startedWatchPid;

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
            string graphqlRemaining = "5000",
            bool staleBaseRefOid = false,
            bool moveHeadDuringFetch = false,
            bool moveBaseDuringFetch = false,
            int failingExitCode = 93,
            int failingPr = 0,
            string hangingTarget = "",
            string failingGhOperation = "",
            int truthGraphDirtyRounds = 1)
        {
            this.failingTarget = failingTarget;
            this.failingExitCode = failingExitCode;
            this.failingPr = failingPr;
            this.hangingTarget = hangingTarget;
            this.failingGhOperation = failingGhOperation;
            this.moveHeadBeforePush = moveHeadBeforePush;
            this.failMergeWithoutConflict = failMergeWithoutConflict;
            this.headBranch = headBranch;
            this.pauseWorktreeCreation = pauseWorktreeCreation;
            this.delayFirstLockOwnerRead = delayFirstLockOwnerRead;
            this.conflicting = conflicting;
            this.ledgerConflict = ledgerConflict;
            this.graphqlRemaining = graphqlRemaining;
            this.staleBaseRefOid = staleBaseRefOid;
            this.moveHeadDuringFetch = moveHeadDuringFetch;
            this.moveBaseDuringFetch = moveBaseDuringFetch;
            this.truthGraphDirtyRounds = truthGraphDirtyRounds;
            origin = Path.Combine(temporary.Path, "origin.git");
            repository = Path.Combine(temporary.Path, "repository");
            seed = Path.Combine(temporary.Path, "seed");
            bin = Path.Combine(temporary.Path, "bin");
            log = Path.Combine(temporary.Path, "shepherd.log");
            calls = Path.Combine(temporary.Path, "mutation-calls");
            boundedCalls = Path.Combine(temporary.Path, "bounded-calls");
            hangingPids = Path.Combine(temporary.Path, "hanging-pids");
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
            Write(seed, "Trureturing.lean", "base trureturing\n");
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
            Write(seed, "Trureturing.lean", "candidate trureturing\n");
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
            Write(seed, "Trureturing.lean", "base trureturing\n");
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
            Git(repository, "config", "user.name", "Fixture");
            Git(repository, "config", "user.email", "fixture@example.invalid");
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

        internal string WatchStatePath => Path.Combine(temporary.Path, "shepherd.pid");

        internal string WatchOwnerPath => WatchStatePath + ".lock";

        internal string RecalculationState(int pullRequest) =>
            File.ReadAllText(Path.Combine(StateDirectory, $"recalculate-{pullRequest}"));

        internal bool InfrastructureStateExists =>
            File.Exists(Path.Combine(StateDirectory, "infrastructure"));

        internal string InfrastructureState() =>
            File.ReadAllText(Path.Combine(StateDirectory, "infrastructure"));

        internal bool RecalculationStateExists(int pullRequest) =>
            File.Exists(Path.Combine(StateDirectory, $"recalculate-{pullRequest}"));

        internal bool DerivedLeaseExists =>
            Directory.Exists(Path.Combine(StateDirectory, "derived-fifo.lease"));

        internal ShepherdResult Run(
            bool dryRun = false,
            bool expiryFingerprint = true,
            bool duplicatePrRow = false,
            bool splitFingerprintAcrossJobs = false,
            bool twoDerivedPrRows = false,
            int? leaseTtlSeconds = null,
            bool derivedPr = true,
            bool diffFailure = false,
            int? statusRollupCount = null,
            IReadOnlyDictionary<string, string>? environment = null,
            bool noChecks = false)
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
                $"PR_TEST_BOUNDED_CALLS={boundedCalls}",
                $"PR_TEST_HANGING_PIDS={hangingPids}",
                $"PR_TEST_EXPIRY={(expiryFingerprint ? "1" : "0")}",
                $"PR_TEST_SPLIT={(splitFingerprintAcrossJobs ? "1" : "0")}",
                $"PR_TEST_DUPLICATE={(duplicatePrRow ? "1" : "0")}",
                $"PR_TEST_TWO_DERIVED={(twoDerivedPrRows ? "1" : "0")}",
                $"PR_TEST_DERIVED={(derivedPr ? "1" : "0")}",
                $"PR_TEST_DIFF_FAILURE={(diffFailure ? "1" : "0")}",
                $"PR_TEST_STATUS_ROLLUP_COUNT={statusRollupCount?.ToString() ?? string.Empty}",
                $"PR_TEST_NO_CHECKS={(noChecks ? "1" : "0")}",
                $"PR_TEST_FAIL_TARGET={failingTarget}",
                $"PR_TEST_FAIL_EXIT={failingExitCode}",
                $"PR_TEST_FAIL_PR={failingPr}",
                $"PR_TEST_HANG_TARGET={hangingTarget}",
                $"PR_TEST_FAIL_GH_OPERATION={failingGhOperation}",
                $"PR_TEST_MOVE_HEAD={(moveHeadBeforePush ? "1" : "0")}",
                $"PR_TEST_FAIL_MERGE={(failMergeWithoutConflict ? "1" : "0")}",
                $"PR_TEST_PAUSE_WORKTREE={(pauseWorktreeCreation ? "1" : "0")}",
                $"PR_TEST_DELAY_LOCK_READ={(delayFirstLockOwnerRead ? "1" : "0")}",
                $"PR_TEST_CONFLICTING={(conflicting ? "1" : "0")}",
                $"PR_TEST_LEDGER_CONFLICT={(ledgerConflict ? "1" : "0")}",
                $"PR_TEST_MOVE_HEAD_DURING_FETCH={(moveHeadDuringFetch ? "1" : "0")}",
                $"PR_TEST_MOVE_BASE_DURING_FETCH={(moveBaseDuringFetch ? "1" : "0")}",
                $"PR_TEST_MOVED_BASE={MovedBaseHead}",
                $"PR_TEST_TRUTH_GRAPH_DIRTY_ROUNDS={truthGraphDirtyRounds}",
                $"PR_TEST_LOCK_READ_MARKER={Path.Combine(temporary.Path, "lock-read-marker")}",
                $"SHEPHERD_DRYRUN={(dryRun ? "1" : "0")}",
                $"PR_TEST_GRAPHQL_REMAINING={graphqlRemaining}",
                "PR_SHEPHERD_WAKE_SLEEP_SECONDS=0",
                "GH_TOKEN=must-not-reach-candidate-producers",
                "/bin/bash",
                script,
                "sweep",
            };
            if (environment is not null)
            {
                foreach (var (name, value) in environment)
                {
                    arguments.Insert(arguments.Count - 3, $"{name}={value}");
                }
            }
            if (leaseTtlSeconds is not null)
            {
                arguments.Insert(
                    arguments.Count - 3,
                    $"PR_SHEPHERD_LEASE_TTL_SECONDS={leaseTtlSeconds.Value}");
            }
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

        internal ShepherdResult RunWatch(
            bool noChecks = false,
            bool dryRun = true,
            IReadOnlyDictionary<string, string>? environment = null) =>
            RunWatchCommand(
                "watch",
                ["0", "1"],
                noChecks,
                TimeSpan.FromSeconds(30),
                dryRun,
                environment);

        internal ShepherdResult RunStart(
            int intervalSeconds = 30,
            int maxCycles = 1,
            bool dryRun = true,
            IReadOnlyDictionary<string, string>? environment = null)
        {
            var result = RunWatchCommand(
                "start",
                [intervalSeconds.ToString(), maxCycles.ToString()],
                noChecks: false,
                TimeSpan.FromSeconds(15),
                dryRun,
                environment);
            if (File.Exists(WatchOwnerPath)) startedWatchPid = ReadOwnerPid();
            return result;
        }

        internal ShepherdResult RunTrackedSweep(
            IReadOnlyDictionary<string, string>? environment = null) =>
            RunWatchCommand(
                "sweep",
                [],
                noChecks: false,
                TimeSpan.FromSeconds(30),
                dryRun: false,
                environment);

        internal ShepherdResult RunStatus() =>
            RunWatchCommand("status", [], noChecks: false, TimeSpan.FromSeconds(10));

        private ShepherdResult RunWatchCommand(
            string command,
            IReadOnlyCollection<string> commandArguments,
            bool noChecks,
            TimeSpan timeout,
            bool dryRun = true,
            IReadOnlyDictionary<string, string>? environment = null)
        {
            EnsureTrackedWatchScripts();
            var script = Path.Combine(repository, ShepherdScriptPath);
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
                $"PR_SHEPHERD_PID={WatchStatePath}",
                $"PR_SHEPHERD_STATE={StateDirectory}",
                $"PR_SHEPHERD_CACHE={CacheRoot}",
                $"PR_TEST_ORIGIN={origin}",
                $"PR_TEST_HEAD={headBranch}",
                $"PR_TEST_BASE_OID={GithubBaseRefOid}",
                $"PR_TEST_CALLS={calls}",
                $"PR_TEST_BOUNDED_CALLS={boundedCalls}",
                $"PR_TEST_HANGING_PIDS={hangingPids}",
                $"PR_TEST_WATCH_STATE={Path.Combine(temporary.Path, "watch-state")}",
                "PR_TEST_EXPIRY=1",
                "PR_TEST_SPLIT=0",
                "PR_TEST_DUPLICATE=0",
                $"PR_TEST_FAIL_TARGET={failingTarget}",
                $"PR_TEST_FAIL_EXIT={failingExitCode}",
                $"PR_TEST_FAIL_PR={failingPr}",
                $"PR_TEST_HANG_TARGET={hangingTarget}",
                $"PR_TEST_FAIL_GH_OPERATION={failingGhOperation}",
                "PR_TEST_MOVE_HEAD=0",
                "PR_TEST_FAIL_MERGE=0",
                "PR_TEST_PAUSE_WORKTREE=0",
                "PR_TEST_DELAY_LOCK_READ=0",
                $"PR_TEST_LEDGER_CONFLICT={(ledgerConflict ? "1" : "0")}",
                "PR_TEST_MOVE_HEAD_DURING_FETCH=0",
                "PR_TEST_MOVE_BASE_DURING_FETCH=0",
                $"PR_TEST_MOVED_BASE={MovedBaseHead}",
                $"PR_TEST_TRUTH_GRAPH_DIRTY_ROUNDS={truthGraphDirtyRounds}",
                $"PR_TEST_LOCK_READ_MARKER={Path.Combine(temporary.Path, "lock-read-marker")}",
                "PR_TEST_WATCH=1",
                $"PR_TEST_NO_CHECKS={(noChecks ? "1" : "0")}",
                $"SHEPHERD_DRYRUN={(dryRun ? "1" : "0")}",
                "/bin/bash",
                script,
                command,
            };
            if (environment is not null)
            {
                var commandIndex = arguments.IndexOf("/bin/bash");
                foreach (var (name, value) in environment)
                {
                    arguments.Insert(commandIndex++, $"{name}={value}");
                }
            }
            arguments.AddRange(commandArguments);
            var result = BoundedProcessRunner.Run(
                "/usr/bin/env",
                arguments,
                repository,
                timeout,
                256 * 1024);
            return new ShepherdResult(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError),
                File.Exists(log) ? File.ReadAllText(log) : string.Empty);
        }

        private void EnsureTrackedWatchScripts()
        {
            var script = Path.Combine(repository, ShepherdScriptPath);
            if (File.Exists(script)) return;
            var leaseScript = Path.Combine(repository, ShepherdLeaseScriptPath);
            var actionsScript = Path.Combine(repository, ShepherdActionsScriptPath);
            var ledgerScript = Path.Combine(repository, ShepherdLedgerScriptPath);
            var fixedPointScript = Path.Combine(repository, ShepherdFixedPointScriptPath);
            var watchScript = Path.Combine(repository, ShepherdWatchScriptPath);
            var wakeScript = Path.Combine(repository, ShepherdWakeScriptPath);
            Directory.CreateDirectory(Path.GetDirectoryName(script)!);
            Directory.CreateDirectory(Path.GetDirectoryName(leaseScript)!);
            File.Copy(Path.Combine(FindRepositoryRoot(), ShepherdScriptPath), script);
            File.Copy(Path.Combine(FindRepositoryRoot(), ShepherdLeaseScriptPath), leaseScript);
            File.Copy(Path.Combine(FindRepositoryRoot(), ShepherdActionsScriptPath), actionsScript);
            File.Copy(Path.Combine(FindRepositoryRoot(), ShepherdLedgerScriptPath), ledgerScript);
            File.Copy(Path.Combine(FindRepositoryRoot(), ShepherdFixedPointScriptPath), fixedPointScript);
            File.Copy(Path.Combine(FindRepositoryRoot(), ShepherdWatchScriptPath), watchScript);
            File.Copy(Path.Combine(FindRepositoryRoot(), ShepherdWakeScriptPath), wakeScript);
            Git(
                repository,
                "add",
                ShepherdScriptPath,
                ShepherdLeaseScriptPath,
                ShepherdActionsScriptPath,
                ShepherdLedgerScriptPath,
                ShepherdFixedPointScriptPath,
                ShepherdWatchScriptPath,
                ShepherdWakeScriptPath);
            Git(repository, "commit", "-m", "track pr-shepherd fixture");
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

        internal ShepherdResult RunOpen(bool ghAppAvailable)
        {
            if (ghAppAvailable)
            {
                WriteExecutable(
                    "gh-app",
                    """
                    #!/usr/bin/env bash
                    set -euo pipefail
                    printf 'api|%s|%s|gh-app %s\n' \
                      "${PR_SHEPHERD_BOUND_STEP-}" \
                      "${PR_SHEPHERD_BOUND_TIMEOUT_SECONDS-}" "$*" \
                      >> "$PR_TEST_BOUNDED_CALLS"
                    [[ "$*" == "token --auto" ]] || exit 96
                    printf '%s\n' "$PR_TEST_GH_APP_TOKEN"
                    """);
            }

            var script = Path.Combine(FindRepositoryRoot(), ShepherdScriptPath);
            var home = Path.Combine(temporary.Path, "home");
            Directory.CreateDirectory(home);
            var result = BoundedProcessRunner.Run(
                "/usr/bin/env",
                [
                    "-u",
                    "GH_TOKEN",
                    "-u",
                    "GITHUB_TOKEN",
                    $"PATH={bin}:/opt/homebrew/bin:/usr/bin:/bin",
                    $"HOME={home}",
                    "PR_SHEPHERD_REPO=the-omega-institute/trureturing",
                    $"PR_SHEPHERD_LOG={log}",
                    $"PR_TEST_CALLS={calls}",
                    $"PR_TEST_BOUNDED_CALLS={boundedCalls}",
                    $"PR_TEST_GH_APP_TOKEN={GhAppToken}",
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

        internal void WriteDerivedLease(int pullRequest, long acquiredAt)
        {
            var leaseDirectory = Path.Combine(StateDirectory, "derived-fifo.lease");
            Directory.CreateDirectory(leaseDirectory);
            File.WriteAllText(
                Path.Combine(leaseDirectory, "owner"),
                $"schema=derived-fifo-lease-v1\n"
                + $"pr={pullRequest}\n"
                + $"acquired_at={acquiredAt}\n"
                + "token=fixture-owner\n",
                new UTF8Encoding(false));
        }

        internal void WriteIncompleteDerivedLease()
        {
            var leaseDirectory = Path.Combine(StateDirectory, "derived-fifo.lease");
            Directory.CreateDirectory(leaseDirectory);
        }

        internal void UseGnuStatWithMtime(long epochSeconds) =>
            WriteExecutable(
                "stat",
                $$"""
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "${1:-}" == "-f" && "${2:-}" == "%m" ]]; then
                  printf '%s\n' '/'
                  exit 0
                fi
                if [[ "${1:-}" == "-c" && "${2:-}" == "%Y" ]]; then
                  printf '%s\n' '{{epochSeconds}}'
                  exit 0
                fi
                exit 64
                """);

        internal void UseFixedClock(long epochSeconds) =>
            WriteExecutable(
                "date",
                $"""
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "$*" == "+%s" ]]; then
                  printf '%s\n' '{epochSeconds}'
                  exit 0
                fi
                exec /bin/date "$@"
                """);

        internal void MoveHeadToAttacker() =>
            Git(temporary.Path, "--git-dir", origin, "update-ref", $"refs/heads/{headBranch}", AttackerHead);

        internal string WakeState() =>
            File.ReadAllText(Path.Combine(StateDirectory, "nochecks-1"));

        internal bool WakeStateExists() =>
            File.Exists(Path.Combine(StateDirectory, "nochecks-1"));

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

        internal string[] BoundedCalls() =>
            File.Exists(boundedCalls) ? File.ReadAllLines(boundedCalls) : [];

        internal string[] LedgerObservations() =>
            File.Exists(calls + ".ledger") ? File.ReadAllLines(calls + ".ledger") : [];

        internal string[] FixedPointObservations() =>
            File.Exists(calls + ".fixed-point")
                ? File.ReadAllLines(calls + ".fixed-point")
                : [];

        internal int[] HangingProcessIds() =>
            File.Exists(hangingPids)
                ? File.ReadAllLines(hangingPids).Select(int.Parse).ToArray()
                : [];

        internal bool IsProcessAlive(int pid) =>
            BoundedProcessRunner.Run(
                "/bin/kill",
                ["-0", pid.ToString()],
                repository,
                TimeSpan.FromSeconds(2),
                4 * 1024).ExitCode == 0;

        internal void ClearMutationCalls() => File.Delete(calls);

        internal void ClearBoundedCalls() => File.Delete(boundedCalls);

        internal void SetFailingTarget(string target) => failingTarget = target;

        internal void SetFailingGhOperation(string operation) => failingGhOperation = operation;

        internal void CommitTrackedHelperChange(string marker)
        {
            EnsureTrackedWatchScripts();
            var helper = Path.Combine(repository, ShepherdActionsScriptPath);
            File.AppendAllText(helper, $"\n# {marker}\n", new UTF8Encoding(false));
            Git(repository, "add", ShepherdActionsScriptPath);
            Git(repository, "commit", "-m", marker);
        }

        internal void CommitTrackedLedgerHelperChange(string marker)
        {
            EnsureTrackedWatchScripts();
            var helper = Path.Combine(repository, ShepherdLedgerScriptPath);
            File.AppendAllText(helper, $"\n# {marker}\n", new UTF8Encoding(false));
            Git(repository, "add", ShepherdLedgerScriptPath);
            Git(repository, "commit", "-m", marker);
        }

    }

    private sealed record ShepherdResult(int ExitCode, string Output, string Error, string Log);

    private sealed record CommandResult(int ExitCode, string Output, string Error);
}
