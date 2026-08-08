using System.Reflection;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection(PrShepherdWallClockCollection.Name)]
public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void WallClockShepherdFixturesUseANonParallelCollection()
    {
        var collection = Assert.Single(
            CustomAttributeData.GetCustomAttributes(typeof(PrShepherdRecalculationTests)),
            attribute => attribute.AttributeType == typeof(CollectionAttribute));
        var collectionName = Assert.IsType<string>(Assert.Single(collection.ConstructorArguments).Value);
        var definition = Assert.Single(
            typeof(PrShepherdRecalculationTests).Assembly.GetTypes()
                .SelectMany(CustomAttributeData.GetCustomAttributes),
            attribute => attribute.AttributeType == typeof(CollectionDefinitionAttribute)
                && Assert.IsType<string>(Assert.Single(attribute.ConstructorArguments).Value) == collectionName);
        var disableParallelization = Assert.Single(definition.NamedArguments);

        Assert.Equal(nameof(CollectionDefinitionAttribute.DisableParallelization), disableParallelization.MemberName);
        Assert.True(Assert.IsType<bool>(disableParallelization.TypedValue.Value));
    }

    [Fact]
    public void SelfContinuationSnapshotContainsTheCompleteShepherdModuleSet()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var started = fixture.RunStart(intervalSeconds: 30, maxCycles: 2);
        Assert.Equal(0, started.ExitCode);
        fixture.WaitForWatchPhase("waiting");

        var loadedScript = fixture.WatchStateField("loaded_script");
        var expectedModules = Directory.GetFiles(
                Path.Combine(FindRepositoryRoot(), "Meta/StrataLint/scripts/shepherd"),
                "pr-shepherd-*.sh")
            .Select(Path.GetFileName)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var actualModules = Directory.GetFiles(
                Path.Combine(Path.GetDirectoryName(loadedScript)!, "shepherd"),
                "pr-shepherd-*.sh")
            .Select(Path.GetFileName)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.True(File.Exists(loadedScript), loadedScript);
        Assert.Equal(expectedModules, actualModules);
    }

    [Fact]
    public void SelfContinuationMissingModulesPublishesAClassifiedTerminalOutcome()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = FindRepositoryRoot();
        var snapshotRoot = Path.Combine(temporary.Path, "pr-shepherd-watch.fixture");
        var snapshot = Path.Combine(snapshotRoot, "pr-shepherd.sh");
        var state = Path.Combine(temporary.Path, "watch.state");
        var log = Path.Combine(temporary.Path, "watch.log");
        var wrapper = Path.Combine(temporary.Path, "reexec.sh");
        Directory.CreateDirectory(snapshotRoot);
        File.Copy(Path.Combine(root, ShepherdScriptPath), snapshot);
        File.WriteAllText(
            wrapper,
            """
            #!/usr/bin/env bash
            set -euo pipefail
            process_start="fixture-process-$$"
            loaded_script="$(cd "$(dirname "$PR_TEST_SNAPSHOT")" && pwd -P)/${PR_TEST_SNAPSHOT##*/}"
            cat > "$PR_TEST_STATE.lock" <<EOF
            schema=pr-watch-owner-v1
            pid=$$
            process_start=$process_start
            canonical_script=$PR_TEST_CANONICAL
            EOF
            cat > "$PR_TEST_STATE" <<EOF
            schema=pr-watch-state-v2
            pid=$$
            process_start=$process_start
            canonical_script=$PR_TEST_CANONICAL
            loaded_script=$loaded_script
            loaded_blob=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
            interval=30
            max_cycles=2
            phase=waiting
            current_pr=none
            current_step=sleep
            step_started_at=100
            step_deadline_at=130
            last_progress_at=100
            last_outcome=sweep-complete
            cycle=1
            terminal_exit=none
            EOF
            exec /usr/bin/env \
              PR_SHEPHERD_CANONICAL_SCRIPT="$PR_TEST_CANONICAL" \
              PR_SHEPHERD_ROOT="$PR_TEST_ROOT" \
              PR_SHEPHERD_LOG="$PR_TEST_LOG" \
              PR_SHEPHERD_PID="$PR_TEST_STATE" \
              PR_SHEPHERD_WATCH_LOADED_BLOB=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \
              PR_SHEPHERD_WATCH_PROCESS_START="$process_start" \
              /bin/bash "$loaded_script" watch 30 2
            """,
            new UTF8Encoding(false));

        var result = BoundedProcessRunner.Run(
            "/usr/bin/env",
            [
                $"PR_TEST_CANONICAL={Path.Combine(root, ShepherdScriptPath)}",
                $"PR_TEST_ROOT={root}",
                $"PR_TEST_LOG={log}",
                $"PR_TEST_STATE={state}",
                $"PR_TEST_SNAPSHOT={snapshot}",
                "/bin/bash",
                wrapper,
            ],
            root,
            TimeSpan.FromSeconds(10),
            64 * 1024);

        Assert.Equal(1, result.ExitCode);
        var logContents = File.ReadAllText(log);
        var stateContents = File.ReadAllText(state);
        Assert.Contains("reason=missing-modules", logContents, StringComparison.Ordinal);
        Assert.True(
            stateContents.Contains("last_outcome=exit-1-missing-modules", StringComparison.Ordinal),
            $"state:\n{stateContents}\nlog:\n{logContents}\nstderr:\n{Encoding.UTF8.GetString(result.StandardError)}");
    }

    [Fact]
    public void ActiveBranchLockPreventsConcurrentWorktreeMutation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var plan = fixture.Run(dryRun: true);
        fixture.HoldBranchLock(DryRunWorktreeName(plan.Log));

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Empty(fixture.MutationCalls());
        Assert.Contains("已有重算实例,跳过本轮", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void SanitizedBranchSlugsRemainCollisionResistant()
    {
        if (OperatingSystem.IsWindows()) return;
        using var slash = new ShepherdFixture(headBranch: "topic/a");
        var slashResult = slash.Run(dryRun: true);
        var slashWorktree = DryRunWorktreeName(slashResult.Log);
        using var literal = new ShepherdFixture(headBranch: slashWorktree[3..]);
        var literalResult = literal.Run(dryRun: true);

        Assert.Equal(0, slashResult.ExitCode);
        Assert.Equal(0, literalResult.ExitCode);
        Assert.NotEqual(slashWorktree, DryRunWorktreeName(literalResult.Log));
    }

    [Fact]
    public async Task ConcurrentStaleLockReclamationAllowsOnlyOneRecalculation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(
            pauseWorktreeCreation: true,
            delayFirstLockOwnerRead: true);
        var plan = fixture.Run(dryRun: true);
        fixture.CreateStaleBranchLock(DryRunWorktreeName(plan.Log));

        var results = await Task.WhenAll(
            Task.Run(() => fixture.Run()),
            Task.Run(() => fixture.Run()));

        Assert.All(results, result => Assert.Equal(0, result.ExitCode));
        Assert.Equal(1, fixture.MutationCalls().Count(call => call == "push"));
        Assert.Equal(1, fixture.CountCommitsWithSubject(CommitSubject));
    }

    [Fact]
    public void StaleLockReclamationUsesAtomicRenameOwnership()
    {
        var script = ReadShepherdScripts();

        AssertInOrder(
            script,
            "mkdir \"$reap\"",
            "owner=\"$(cat \"$lock/pid\"",
            "mv \"$lock\" \"$stale\"");
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
                "DRYRUN #1 RECALCULATE -> ensure worktree",
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
}

[CollectionDefinition(PrShepherdWallClockCollection.Name, DisableParallelization = true)]
public sealed class PrShepherdWallClockCollection
{
    public const string Name = "PR shepherd wall-clock fixtures";
}
