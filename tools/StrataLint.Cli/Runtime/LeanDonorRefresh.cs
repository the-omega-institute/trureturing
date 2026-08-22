namespace StrataLint.Cli;

/// <summary>
/// 把货源刷新到当前 dev，然后才让 worktree 从它 clone。
///
/// 主检出是 Lean 缓存的唯一真源，每棵 worktree 都是它的投影。`SelectDonor` 早已优先
/// 选主检出，缺的一直是「选中之后没有人保证它是新的」——实测它停在七天前
/// (.lake/build 日期 Aug 15，而 dev 已推进数千提交)，于是新 worktree 明明 ensure
/// 成功，仍要补七天的差量(实测 57 分钟)。ensure 没坏，是它的货源太旧。
///
/// 刷新是**写**操作，故走既有锁协议的排他端；clone 走共享端。二者串行，
/// 因为刷新期间 `lake build` 会让 `LeanCacheBusyProbe` 判 donor 忙，
/// 与 clone 交错会让紧随其后的 clone 被拒。
///
/// 全程尽力而为：任何一步失败都不得挡住调用者构建——它仍可用货源里现有的东西。
/// 加速器不把关，这与 `fetch` 对依赖层身份 fail-closed 不矛盾：那里守正确性，这里只守速度。
/// </summary>
internal static class LeanDonorRefresh
{
    internal static string TryRefresh(
        string donorRoot,
        string worktreeRoot,
        IWorktreeProcessRunner runner)
    {
        ArgumentNullException.ThrowIfNull(runner);

        // 主检出自己构建时不刷新自己：它就是货源，递归刷新会自己等自己。
        if (string.Equals(
                LeanCacheGuard.PhysicalPath(donorRoot),
                LeanCacheGuard.PhysicalPath(worktreeRoot),
                StringComparison.Ordinal))
        {
            return "skipped: the caller is the donor";
        }

        var lake = Path.Combine(donorRoot, ".lake");
        if (!Directory.Exists(donorRoot)) return "skipped: donor root is absent";

        // 拿不到排他锁不是错误：别人正在刷新，其结果正是这里要产生的。
        using var guard = LeanCacheGuard.TryAcquireExclusive(lake);
        if (guard is null) return "skipped: another refresh holds the donor lock";

        var pulled = Run(runner, donorRoot, "git", ["pull", "--ff-only", "--quiet", "origin", "dev"]);

        var fetched = "not-needed";
        if (CountOleans(lake) == 0)
        {
            // 一份已发布的归档胜过从零编译。fetch 会回退到同 config 的最近一份，
            // 落地一个近期基底而非要求 dev 早已跑过头的精确地址。
            fetched = Run(
                runner,
                donorRoot,
                "/bin/bash",
                [Path.Combine(donorRoot, "tools", "scripts", "worktree", "lean-cache-publish.sh"),
                 "fetch", "--repository", donorRoot]);
        }

        // 无论走哪条路都做增量：lake 会 replay 仍然有效的部分，只编译 dev 引入的差量。
        // 货源本就热时，这一步接近 no-op。
        var built = Run(runner, donorRoot, "lake", ["build"]);

        return $"pulled={pulled} fetched={fetched} built={built} olean={CountOleans(lake)}";
    }

    private static int CountOleans(string lake)
    {
        var build = Path.Combine(lake, "build");
        if (!Directory.Exists(build)) return 0;
        try
        {
            return Directory.EnumerateFiles(build, "*.olean", SearchOption.AllDirectories).Count();
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            return 0;
        }
    }

    private static string Run(
        IWorktreeProcessRunner runner,
        string workingDirectory,
        string executable,
        string[] arguments)
    {
        try
        {
            var output = runner.Run(executable, arguments, workingDirectory, TimeSpan.FromSeconds(
                LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds));
            return output.ExitCode == 0 ? "ok" : $"exit{output.ExitCode}";
        }
        catch (Exception exception) when (exception is IOException
            or UnauthorizedAccessException
            or InvalidOperationException
            or TimeoutException)
        {
            return "error";
        }
    }
}
