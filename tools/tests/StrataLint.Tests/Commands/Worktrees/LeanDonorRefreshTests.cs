namespace StrataLint.Tests;

/// <summary>
/// 主检出是 Lean 缓存的唯一真源，worktree 都是它的投影。`SelectDonor` 早已优先选它，
/// 缺的是「选中之后没人保证它是新的」——实测停在七天前，于是 ensure 成功却仍要
/// 补七天差量(57 分钟)。这里钉住刷新那一步的四条承重契约。
/// </summary>
/// <remarks>
/// 关于 <c>LeanCacheEnsureCommandTests</c> 里那两条 lake 断言为何限于**目标树**:
/// 那两个测试守的是「staging 不完整时不得在目标树上做昂贵操作」。货源刷新在 donor
/// 上跑 lake，与目标树的完整性无关，原断言不区分工作目录才会把它一并判红。
/// 删掉断言能让它们变绿，但会把契约一起丢掉，故只限定范围。变异证明:让生产代码
/// 在目标树内跑 lake（契约明禁之事），两条断言仍红。
/// </remarks>
public sealed class LeanDonorRefreshTests
{
    private static string Refresh() => TestRepositoryLayout.ReadAllText(
        RepositoryRelativePath.Create("tools/StrataLint.Cli/Runtime/LeanDonorRefresh.cs"));

    private static string Caller() => TestRepositoryLayout.ReadAllText(
        RepositoryRelativePath.Create("tools/StrataLint.Cli/Commands/Worktrees/LeanCacheEnsureCommand.cs"));

    /// <summary>
    /// 刷新必须发生在 clone 之前，且在 `make lean` 的必经路径上。
    /// 做成可选预热等于没有:被跳过时的症状只是「构建慢」，不会有任何东西变红。
    /// </summary>
    [Fact]
    public void EveryPathThatClonesFromTheDonorRefreshesItFirst()
    {
        var caller = Caller();
        // 调用点计数,不含方法定义本身。用「第一个 clone 点」做判据是坏的:
        // 文件里有两个入口(`make lean` 的 writer 路径与 `make lean-cache-ensure`),
        // 只覆盖其一时 IndexOf 仍会指向另一个,红绿都不说明问题。
        var clones = System.Text.RegularExpressions.Regex.Matches(
            caller, @"(return|var ensured =) EnsureLocked\(").Count;
        var refreshes = System.Text.RegularExpressions.Regex.Matches(
            caller, @"LeanDonorRefresh\.TryRefresh\(").Count;
        Assert.True(clones > 0, "the file must still clone from a donor somewhere");
        Assert.Equal(clones, refreshes);
    }

    /// <summary>
    /// 刷新是写操作，必须走既有锁协议的**排他**端。自搓一套锁比不加锁更危险:
    /// 两边各以为自己受保护，而一边在写、另一边在读同一棵树。
    /// </summary>
    [Fact]
    public void RefreshingTakesTheExclusiveEndOfTheExistingGuardProtocol()
    {
        var refresh = Refresh();
        Assert.Contains("LeanCacheGuard.TryAcquireExclusive", refresh, StringComparison.Ordinal);
        // 反向钉住:不得另开一套锁。mkdir/自建锁文件都属此列。
        Assert.DoesNotContain("Directory.CreateDirectory(lock", refresh, StringComparison.Ordinal);
        Assert.DoesNotContain(".donor-refresh.lock", refresh, StringComparison.Ordinal);
    }

    /// <summary>
    /// 主检出自己构建时不刷新自己——它就是货源，递归刷新会自己等自己。
    /// 判定必须用与选 donor 相同的路径规范化，否则符号链接或大小写差异会让它失效。
    /// </summary>
    [Fact]
    public void TheDonorDoesNotRefreshItself()
    {
        var refresh = Refresh();
        Assert.Contains("LeanCacheGuard.PhysicalPath(donorRoot)", refresh, StringComparison.Ordinal);
        Assert.Contains("LeanCacheGuard.PhysicalPath(worktreeRoot)", refresh, StringComparison.Ordinal);
        Assert.Contains("skipped: the caller is the donor", refresh, StringComparison.Ordinal);
    }

    /// <summary>
    /// 尽力而为:抢不到锁、pull 失败、fetch 失败、build 失败，都只是少一次加速，
    /// 绝不挡住本次构建。加速器不把关——这与 `fetch` 对依赖层身份 fail-closed 不矛盾:
    /// 那里守正确性，这里只守速度。
    /// </summary>
    [Fact]
    public void ARefreshFailureNeverBlocksTheBuildItPrecedes()
    {
        var refresh = Refresh();
        Assert.Contains("skipped: another refresh holds the donor lock", refresh, StringComparison.Ordinal);
        Assert.Contains("skipped: donor root is absent", refresh, StringComparison.Ordinal);
        // 返回诊断字符串而非抛出或返回失败码:调用方无从被它中断。
        Assert.Contains("internal static string TryRefresh(", refresh, StringComparison.Ordinal);
    }
}

/// <summary>
/// `LeanCacheEnsureCommandTests` 那两条 lake 断言限于**目标树**的判据。
/// 那两个测试守的是「staging 不完整时不得在目标树上做昂贵操作」;货源刷新在 donor 上
/// 跑 lake，与目标树完整性无关，原断言不区分工作目录才会把它一并判红。删掉断言能让它们
/// 变绿却会把契约一起丢掉，故只限定范围。变异证明:让生产代码在目标树内跑 lake
/// (契约明禁之事)，两条断言仍红。
/// </summary>
internal static class LeanCachePredicates
{
    internal static bool IsLakeInTarget(WorktreeProcessInvocation call, string target) =>
        call.FileName == "lake"
            && call.WorkingDirectory.StartsWith(target, StringComparison.Ordinal);
}

