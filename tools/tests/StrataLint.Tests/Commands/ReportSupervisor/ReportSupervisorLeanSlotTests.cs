using System.Text;

namespace StrataLint.Tests;

// Lean 槽的容量命题独立成篇:它谈的是编排(几个 producer 能同时跑),与同目录那篇谈脚本
// 契约(退出码、指标、进程树回收)的测试不是同一件事。2026-08-15 因默认槽数由 1 改为 3
// 而重写时,原文件已 790 行、逼近 SL-003 的 800 硬线,顺势按第8条裂到既有子目录。
public sealed class ReportSupervisorLeanSlotTests
{
    [Fact]
    public void ConcurrencyFixtureUsesReleaseSignalsInsteadOfElapsedWindows()
    {
        var source = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
            "tools/tests/StrataLint.Tests/Commands/ReportSupervisorFixture.cs"));

        Assert.DoesNotContain("sleep 1", source, StringComparison.Ordinal);
        Assert.DoesNotContain("sleep 60", source, StringComparison.Ordinal);
        Assert.DoesNotContain("exec \"sleep\", \"60\"", source, StringComparison.Ordinal);
        Assert.Contains("second-acquisition", source, StringComparison.Ordinal);
        Assert.Contains("release.fifo", source, StringComparison.Ordinal);
        Assert.Contains("IFS= read -r _ < \"$2\"", source, StringComparison.Ordinal);
    }

    // 2026-08-15 用户裁决:默认槽数 1 -> 5(同日先定 3,再定 5)。命题因此换了,不是删掉——
    // "槽机制会封顶"仍受钉,
    // 只是封顶值由默认值给出。两条一起看才完整:显式设 1 时仍然串行(机制还在),用默认值时
    // 两个 producer 允许重叠(默认值确实是 >1)。
    //
    // 留档的反对读数(用户已确认后仍要加槽):实测一次 Lean 构建自身即跑 10+ 个 lean 进程、
    // 每个约 85% CPU,全机 top 两次采样 idle 0.12%(28 核 / 96 GB)。故加槽不增吞吐,只把
    // 同样的核分成 N 份。内存不是约束(44 GB 空闲,单次构建总 RSS 11.5 GB)。
    [Fact]
    public void ExplicitSingleLeanSlotStillSerializesConcurrentProducers()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.RunExternalProcess(
            "bash",
            [fixture.ConcurrentDriver, fixture.Supervisor, fixture.ProducerWorker,
             fixture.StateRoot, fixture.ActiveMarker, fixture.OverlapMarker, "1"],
            maximumOutputBytes: 1024 * 1024);

        Assert.True(
            result.ExitCode == 0,
            $"concurrent driver exited {result.ExitCode}; stdout: "
                + Encoding.UTF8.GetString(result.StandardOutput)
                + "; stderr: "
                + Encoding.UTF8.GetString(result.StandardError));
        Assert.False(File.Exists(fixture.OverlapMarker));
    }

    [Fact]
    public void DefaultLeanSlotCountAdmitsConcurrentProducers()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.RunExternalProcess(
            "bash",
            [fixture.ConcurrentDriver, fixture.Supervisor, fixture.ProducerWorker,
             fixture.StateRoot, fixture.ActiveMarker, fixture.OverlapMarker],
            maximumOutputBytes: 1024 * 1024);

        Assert.True(
            result.ExitCode == 0,
            $"concurrent driver exited {result.ExitCode}; stdout: "
                + Encoding.UTF8.GetString(result.StandardOutput)
                + "; stderr: "
                + Encoding.UTF8.GetString(result.StandardError));
        Assert.True(
            File.Exists(fixture.OverlapMarker),
            "the default slot count must admit two concurrent lean producers");
    }
    // 等槽者必须熬得过一个**合法**的持槽者,否则「合法持有」就等于「让别人红」。
    //
    // 2026-08-15 实测该不自洽的代价:LOCK_TIMEOUT_SECONDS 默认 900s(15 分钟)而
    // BUILD_TIMEOUT_SECONDS 默认 7200s(2 小时),差 8 倍。一次持槽 24m24s 的正常构建
    // 直接把等待中的 `make preflight` 判红:
    //     report-supervisor: timed out waiting for a Lean slot
    //     report-supervisor: slot-1.lock holder pid=94189 ... held_for=24m24s
    // 判词说「timed out」,读上去像等待者自己的问题,实则是两个预算的差额造成的。
    // 多 worktree 并行是本仓常态(第16条),所以这不是罕见路径。
    //
    // 钉的是**不变量**而不是某个数:谁改了任一默认值,只要把等待预算压到持有预算之下,
    // 这条就红。剩余的饥饿问题(mkdir 抢占自旋而非 FIFO)是 #1910 的另一半,本条不假装修了它。
    [Fact]
    public void WaiterBudgetOutlastsALegitimateHolder()
    {
        var source = File.ReadAllText(SupervisorScriptPath());
        var wait = DefaultOf(source, "STRATALINT_LOCK_TIMEOUT_SECONDS");
        var hold = DefaultOf(source, "STRATALINT_BUILD_TIMEOUT_SECONDS");

        Assert.True(
            wait >= hold,
            $"a waiter gives up after {wait}s while a holder may legitimately hold {hold}s; "
            + "one legitimate long build would then red every concurrent waiter");
    }

    // 嵌套 deadline 取最小:`make lean-report` 的 worker 构建外层由本脚本的 BUILD_TIMEOUT 兜住,
    // 内层由 `LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds`(policy-override,#2535→#4120)兜住。
    // 若外层小于内层,内层那份「清过当前规模冷建」的论证就是空话——复审线按内层算,
    // 而实际杀进程的是外层(2026-08-30 #4122 architecture 席实测指出:内层已抬到 21600 而外层仍是 7200)。
    // 故外层默认值必须**等于**内层声明值:同一个数只在 C# 声明一次,脚本里的字面量由本条钉住。
    [Fact]
    public void HolderBudgetMatchesTheProvisionPolicyCeiling()
    {
        var source = File.ReadAllText(SupervisorScriptPath());
        var hold = DefaultOf(source, "STRATALINT_BUILD_TIMEOUT_SECONDS");

        Assert.True(
            hold == StrataLint.Cli.LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds,
            $"supervisor BUILD_TIMEOUT default {hold}s != LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds "
            + $"{StrataLint.Cli.LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds}s; nested deadlines take the minimum, "
            + "so the smaller outer value silently replaces the declared policy-override");
    }

    private static int DefaultOf(string source, string name)
    {
        var match = System.Text.RegularExpressions.Regex.Match(
            source,
            @"\$\{" + System.Text.RegularExpressions.Regex.Escape(name) + @":-(?<value>[0-9]+)\}");
        Assert.True(match.Success, $"{name} has no literal default in the supervisor script");
        return int.Parse(
            match.Groups["value"].Value,
            System.Globalization.CultureInfo.InvariantCulture);
    }

    private static string SupervisorScriptPath() =>
        Path.Combine(
            TestRepositoryLayout.FindRoot(), "tools", "scripts", "report", "report-supervisor.sh");

}
