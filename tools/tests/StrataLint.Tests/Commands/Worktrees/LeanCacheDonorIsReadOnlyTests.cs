using StrataLint.Cli;

namespace StrataLint.Tests;

/// <summary>
/// 取缓存时,货源树只许**读**。
///
/// 这条契约取代了它的前身「每条 clone 路径都必须先刷新 donor」。那个设计让
/// `make lean` 去 donor 上跑 `git pull` 与 `lake build`,即从一棵工作树里推进
/// 并重建另一棵——而调用方对那棵树的状态一无所知(它可能不在 dev 上、可能有
/// 未提交改动、可能正在跑 lean-report)。
///
/// 它在生产路径上还从未执行过:`repositoryRoot` 取自 `Environment.CurrentDirectory`
/// (`Program.cs`),而 `lean-cache-run.sh` / `lean-cache-ensure.sh` 都 `cd` 到本树根
/// 且不传 `--path`,于是 donorRoot 与 worktreeRoot 恒等,刷新每次都在第一个分支
/// 返回 `skipped: the caller is the donor`。唯一能让二者不等的调用者是测试夹具。
///
/// 故这里钉的是**行为**而不是源码文本:donor 树内只允许清点式的读,
/// 任何写(`git pull`、`lake build`)都判红——无论未来谁以什么理由把它加回来。
///
/// 连带:<c>LeanCacheEnsureCommandTests</c> 里两条 lake 断言原本限定「不得在**目标树**
/// 跑 lake」,那个范围正是当初为货源刷新在 donor 上跑的 <c>lake build</c> 让出来的。
/// 刷新删除后收回为「clone 成功即不得有任何 lake 调用」。说明只写在这一处。
/// </summary>
public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void SeedingFromADonorNeverRunsAWriteInsideTheDonorTree()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "main repository cache\n");
        var target = AddWorktree(repository.Path, "read-only-donor");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.True(result.Success, result.Error);
        // 白名单而非黑名单:枚举 donor 上**允许**的调用,其余一律违规。
        // 黑名单要穷举写操作的写法,漏一种就漏一个洞。
        var forbidden = runner.Invocations
            .Where(call => IsInsideDonorButNotTarget(call, repository.Path, target))
            .Where(static call => !IsDonorInventoryRead(call))
            .Select(static call => $"{call.FileName} {string.Join(' ', call.Arguments)}")
            .ToArray();
        Assert.Empty(forbidden);
    }

    /// <summary>
    /// 生产形态的对照:`lean-cache-run.sh` / `lean-cache-ensure.sh` 都 cd 到本树根且
    /// 不传 `--path`,故 root 就是 repositoryRoot,货源是一棵**兄弟**工作树。
    ///
    /// 这条同时是阳性对照:先断言收据是 `seeded` 且 donor 正是那棵兄弟树,
    /// 证明确实走完了 clone 路径——否则「没有写」只是因为什么都没发生,
    /// 那种绿不构成证据。
    /// </summary>
    [Fact]
    public void SeedingFromASiblingWorktreeLeavesThatSiblingUntouched()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var warm = AddWorktree(repository.Path, "warm-donor");
        WriteCache(warm, "sibling worktree cache\n");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success, result.Error);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("seeded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal(
            LeanCacheGuard.PhysicalPath(warm),
            receipt.RootElement.GetProperty("donor").GetString());
        var forbidden = runner.Invocations
            .Where(call => call.WorkingDirectory.StartsWith(warm, StringComparison.Ordinal))
            .Select(static call => $"{call.FileName} {string.Join(' ', call.Arguments)}")
            .ToArray();
        Assert.Empty(forbidden);
    }

    /// <summary>
    /// 目标树是 donor 的子目录(`AddWorktree` 建在 `repositoryRoot/name` 下),
    /// 故「落在 donor 内」必须显式排除目标子树,否则判据会把本树自己的合法写算进去。
    /// </summary>
    private static bool IsInsideDonorButNotTarget(
        WorktreeProcessInvocation call,
        string donor,
        string target) =>
        call.WorkingDirectory.StartsWith(donor, StringComparison.Ordinal)
        && !call.WorkingDirectory.StartsWith(target, StringComparison.Ordinal);

    /// <summary>
    /// donor 上唯一正当的调用:清点工作树列表以挑选货源。它不改动任何东西。
    /// </summary>
    private static bool IsDonorInventoryRead(WorktreeProcessInvocation call) =>
        call.FileName == "git"
        && call.Arguments.Take(2).SequenceEqual(["worktree", "list"]);
}
