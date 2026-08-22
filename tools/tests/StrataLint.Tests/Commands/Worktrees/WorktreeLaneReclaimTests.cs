using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// 建新树时,顺手回收已经结束的旧 lane。
///
/// CLAUDE.md 第 16 条早写着「PR 合并即回收该 worktree」,但它只挂在自觉上,没有挂在任何
/// **必然经过**的步骤上——于是仓里长期躺着一批已合入的旧树。`make worktree` 是开新工必
/// 然经过的那一步,把回收挂在这里,那条规则才第一次有了执行点。
///
/// 与已删除的 `LeanDonorRefresh` 的越界不同:那个发现货源陈旧就去 pull + build **别人正在
/// 用**的树,失败还被吞成一个不进收据的字符串。这里回收的是一棵**按仓库政策已经结束**的
/// 树,判据整套继承 clean-lanes(已合入 base ∧ 无未提交改动 ∧ 不是当前树 ∧ 移除前身份复核),
/// 且回收结果整条进 `worktree_init` 收据——失败不吞、不阻断建树、`--no-clean-lanes` 可关。
///
/// 作用域刻意只到 lane:`/tmp` 下的判官树不在此列(席位可能正跑着),要清它们仍走显式的
/// `make -C tools clean-lanes FORCE=1`。这一条由**类型**保证而非由纪律保证——`LanesOnly`
/// 这个 scope 根本没有地方能放 tempRoots。
/// </summary>
public sealed partial class WorktreeCommandTests
{
    [Fact]
    public void MergedCleanLanesAreReclaimedBeforeTheNewLaneIsCreated()
    {
        using var repository = new TemporaryDirectory();
        using var lanes = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var stale = AddLane(repository.Path, lanes.Path, "harness/stale");
        var target = Path.Combine(lanes.Path, "fresh");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["--branch", "harness/fresh", "--path", target, "--base", "dev", "--skip-restore"],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(stale));
        Assert.False(BranchExists(repository.Path, "harness/stale"));
        Assert.True(Directory.Exists(target));
        using var receipt = ParseInitReceipt(result.Output);
        var reclaim = receipt.RootElement.GetProperty("lane_reclaim");
        Assert.Equal("completed", reclaim.GetProperty("status").GetString());
        Assert.Equal(1, reclaim.GetProperty("removed_count").GetInt32());
        Assert.Contains(
            reclaim.GetProperty("removed").EnumerateArray(),
            item => item.GetProperty("path").GetString() == stale
                && item.GetProperty("branch").GetString() == "harness/stale");
    }

    /// <summary>
    /// 回收只认「已结束」,不认「看起来没人管」。脏树可能是别人正在写的工作,未合入的树
    /// 是还没交付的工作——两者都留下,并各自带着理由进收据。
    /// </summary>
    [Fact]
    public void DirtyAndUnmergedLanesSurviveInitialization()
    {
        using var repository = new TemporaryDirectory();
        using var lanes = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var dirty = AddLane(repository.Path, lanes.Path, "harness/dirty");
        File.WriteAllText(Path.Combine(dirty, "scratch.txt"), "uncommitted\n");
        var unmerged = AddLane(repository.Path, lanes.Path, "harness/unmerged");
        File.AppendAllText(Path.Combine(unmerged, "README.md"), "lane work\n");
        ReviewRegressionTests.RunGit(unmerged, "add", "README.md");
        ReviewRegressionTests.RunGit(unmerged, "commit", "-m", "lane work");
        var target = Path.Combine(lanes.Path, "fresh");

        var result = WorktreeCommand.Run(
            repository.Path,
            ["--branch", "harness/fresh", "--path", target, "--base", "dev", "--skip-restore"],
            new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(dirty));
        Assert.True(Directory.Exists(unmerged));
        Assert.True(BranchExists(repository.Path, "harness/dirty"));
        Assert.True(BranchExists(repository.Path, "harness/unmerged"));
        using var receipt = ParseInitReceipt(result.Output);
        var reclaim = receipt.RootElement.GetProperty("lane_reclaim");
        Assert.Equal(0, reclaim.GetProperty("removed_count").GetInt32());
        Assert.Contains(
            reclaim.GetProperty("skipped").EnumerateArray(),
            item => item.GetProperty("path").GetString() == dirty
                && item.GetProperty("reason").GetString() == "dirty");
        Assert.Contains(
            reclaim.GetProperty("skipped").EnumerateArray(),
            item => item.GetProperty("path").GetString() == unmerged
                && item.GetProperty("reason").GetString() == "unmerged");
    }

    /// <summary>
    /// 货源树自己可以正停在一个已合入的 `harness/*` 分支上,判据里那三项它样样满足——
    /// 唯一拦住它的是「这是当前树」。少了这一条,一次建树就会把发起建树的那棵树删掉。
    /// </summary>
    [Fact]
    public void TheDonorItselfIsNeverReclaimed()
    {
        using var repository = new TemporaryDirectory();
        using var lanes = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        ReviewRegressionTests.RunGit(repository.Path, "checkout", "-b", "harness/donor-parked");
        var target = Path.Combine(lanes.Path, "fresh");

        var result = WorktreeCommand.Run(
            repository.Path,
            ["--branch", "harness/fresh", "--path", target, "--base", "dev", "--skip-restore"],
            new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(repository.Path));
        Assert.True(BranchExists(repository.Path, "harness/donor-parked"));
        using var receipt = ParseInitReceipt(result.Output);
        var reclaim = receipt.RootElement.GetProperty("lane_reclaim");
        Assert.Equal(0, reclaim.GetProperty("removed_count").GetInt32());
        Assert.Contains(
            reclaim.GetProperty("skipped").EnumerateArray(),
            item => item.GetProperty("branch").GetString() == "harness/donor-parked"
                && item.GetProperty("reason").GetString() == "current");
    }

    [Fact]
    public void NoCleanLanesKeepsEveryExistingLane()
    {
        using var repository = new TemporaryDirectory();
        using var lanes = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var stale = AddLane(repository.Path, lanes.Path, "harness/stale");
        var target = Path.Combine(lanes.Path, "fresh");

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/fresh",
                "--path", target,
                "--base", "dev",
                "--skip-restore",
                "--no-clean-lanes",
            ],
            new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(stale));
        Assert.True(BranchExists(repository.Path, "harness/stale"));
        using var receipt = ParseInitReceipt(result.Output);
        var reclaim = receipt.RootElement.GetProperty("lane_reclaim");
        Assert.Equal("disabled", reclaim.GetProperty("status").GetString());
        Assert.Equal(0, reclaim.GetProperty("removed_count").GetInt32());
    }

    /// <summary>
    /// 回收是附带动作,建树才是本职:回收坏了不许把建树一起拖红。但也绝不静默——
    /// 状态进收据、原因进收据、stderr 给一条可以直接粘贴执行的排查命令。
    /// </summary>
    [Fact]
    public void ReclaimFailureIsReportedWithoutBlockingTheNewLane()
    {
        using var repository = new TemporaryDirectory();
        using var lanes = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var stale = AddLane(repository.Path, lanes.Path, "harness/stale");
        var target = Path.Combine(lanes.Path, "fresh");
        var runner = new FailingVerbRunner(
            arguments => arguments.Count > 1 && arguments[0] == "worktree" && arguments[1] == "list",
            "synthetic lane enumeration failure");

        var result = WorktreeCommand.Run(
            repository.Path,
            ["--branch", "harness/fresh", "--path", target, "--base", "dev", "--skip-restore"],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(target));
        Assert.True(Directory.Exists(stale));
        using var receipt = ParseInitReceipt(result.Output);
        var reclaim = receipt.RootElement.GetProperty("lane_reclaim");
        Assert.Equal("failed", reclaim.GetProperty("status").GetString());
        Assert.Equal(
            "synthetic lane enumeration failure",
            reclaim.GetProperty("error").GetString());
        Assert.Contains("clean-lanes", result.Error, StringComparison.Ordinal);
    }

    /// <summary>
    /// 判官树不在建树的作用域里。阳性对照同时在场:同一批输入换成 `Full`
    /// 就必须看见它——否则「没看见」只证明这棵树本来就不合判据,不证明 scope 起了作用。
    /// </summary>
    [Fact]
    public void RegisteredLaneScopeCannotReachTempJudgeTrees()
    {
        using var repository = new TemporaryDirectory();
        using var temp = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var judge = WriteGitlessJudgeSnapshot(temp.Path, "trureturing-judge");
        var runner = new RecordingWorktreeProcessRunner();

        var lanesOnly = new List<CleanLanesCommand.CleanLaneEvent>();
        CleanLanesCommand.Inspect(
            repository.Path,
            "dev",
            force: false,
            new CleanLanesCommand.CleanLaneScope.RegisteredLanes(),
            runner,
            lanesOnly);

        var includingJudges = new List<CleanLanesCommand.CleanLaneEvent>();
        CleanLanesCommand.Inspect(
            repository.Path,
            "dev",
            force: false,
            new CleanLanesCommand.CleanLaneScope.Full([temp.Path]),
            runner,
            includingJudges);

        Assert.DoesNotContain(lanesOnly, item => item.Kind == "temp_judge");
        Assert.Contains(
            includingJudges,
            item => item.Kind == "temp_judge" && item.Path == judge);
        Assert.True(Directory.Exists(judge));
    }

    [Fact]
    public void ReclaimIsOnByDefaultAndItsSwitchIsParsedOnce()
    {
        var defaults = WorktreeCommand.ParseArguments(
            "/tmp",
            ["--branch", "harness/probe", "--path", "/tmp/probe"]);
        var disabled = WorktreeCommand.ParseArguments(
            "/tmp",
            ["--branch", "harness/probe", "--path", "/tmp/probe", "--no-clean-lanes"]);

        Assert.True(defaults.ReclaimLanes);
        Assert.False(disabled.ReclaimLanes);
        var exception = Assert.Throws<InvalidOperationException>(() =>
            WorktreeCommand.ParseArguments(
                "/tmp",
                [
                    "--branch", "harness/probe",
                    "--path", "/tmp/probe",
                    "--no-clean-lanes",
                    "--no-clean-lanes",
                ]));
        Assert.Contains("USAGE: StrataLint worktree", exception.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// 返回 git 自己认的那个路径,不是我们拼出来的那个:macOS 上 `/var` 是 `/private/var`
    /// 的符号链接,`worktree list` 报的是解析后的形式,拿拼串去比会必然不等。
    /// </summary>
    /// <summary>
    /// 孤儿分支(已合入、没有树)不占一棵 worktree,删它是纯分支操作——不属于「建树时顺手
    /// 回收旧树」。阳性对照同在:同一个分支在 `Full` 作用域里确实是可回收项,所以「建树
    /// 没删它」是 scope 的功劳,不是这个分支本来就不合判据。
    /// </summary>
    [Fact]
    public void OrphanBranchesAreLeftToTheExplicitCleanLanesGate()
    {
        using var repository = new TemporaryDirectory();
        using var lanes = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        ReviewRegressionTests.RunGit(repository.Path, "branch", "harness/orphan", "dev");
        var target = Path.Combine(lanes.Path, "fresh");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["--branch", "harness/fresh", "--path", target, "--base", "dev", "--skip-restore"],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.True(BranchExists(repository.Path, "harness/orphan"));
        using var receipt = ParseInitReceipt(result.Output);
        Assert.Equal(
            0,
            receipt.RootElement.GetProperty("lane_reclaim").GetProperty("removed_count").GetInt32());

        var full = new List<CleanLanesCommand.CleanLaneEvent>();
        CleanLanesCommand.Inspect(
            repository.Path,
            "dev",
            force: false,
            new CleanLanesCommand.CleanLaneScope.Full([]),
            runner,
            full);
        Assert.Contains(
            full,
            item => item.Kind == "orphan_branch"
                && item.Branch == "harness/orphan"
                && item.Action == "would_remove");
    }

    private static string AddLane(string repositoryRoot, string laneRoot, string branch)
    {
        var path = Path.Combine(laneRoot, branch.Replace('/', '-'));
        ReviewRegressionTests.RunGit(repositoryRoot, "worktree", "add", "-b", branch, path, "dev");
        return ReviewRegressionTests.RunGit(path, "rev-parse", "--show-toplevel").Trim();
    }

    private static bool BranchExists(string repositoryRoot, string branch) =>
        BoundedProcessRunner.Run(
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{branch}"],
            repositoryRoot,
            TimeSpan.FromSeconds(30),
            4096).ExitCode == 0;

    private static string WriteGitlessJudgeSnapshot(string root, string name)
    {
        var path = Path.Combine(root, name);
        Directory.CreateDirectory(Path.Combine(path, "D5"));
        Directory.CreateDirectory(Path.Combine(path, "tools"));
        Directory.CreateDirectory(Path.Combine(path, ".github", "scripts"));
        foreach (var file in new[] { "CLAUDE.md", "AGENTS.md", "Trureturing.lean", "lean-toolchain" })
        {
            File.WriteAllText(Path.Combine(path, file), "judge fixture\n");
        }

        File.WriteAllText(Path.Combine(path, ".github", "scripts", "harness-gate.sh"), "judge\n");
        return Path.GetFullPath(path);
    }

    private sealed class FailingVerbRunner(
        Func<IReadOnlyList<string>, bool> shouldFail,
        string error) : IWorktreeProcessRunner
    {
        private readonly ProductionWorktreeProcessRunner inner = new();

        public ProcessOutput Run(
            string fileName,
            IReadOnlyList<string> arguments,
            string workingDirectory,
            TimeSpan timeout) =>
            fileName == "git" && shouldFail(arguments)
                ? new ProcessOutput(
                    128,
                    [],
                    System.Text.Encoding.UTF8.GetBytes(error + "\n"))
                : inner.Run(fileName, arguments, workingDirectory, timeout);
    }
}
