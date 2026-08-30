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
        // 持有预算按角色取值(#4122):等待者必须熬得过**任一**合法持槽者,故取两者之大。
        var hold = Math.Max(
            LiteralAssignment(source, "LEAN_PRODUCER_BUILD_TIMEOUT_SECONDS"),
            LiteralAssignment(source, "CONSUMER_BUILD_TIMEOUT_SECONDS"));

        Assert.True(
            wait >= hold,
            $"a waiter gives up after {wait}s while a holder may legitimately hold {hold}s; "
            + "one legitimate long build would then red every concurrent waiter");
    }

    // 嵌套 deadline 取最小:`make lean-report` 的 worker(`tools/lean-inspector/inspect.sh`,role=lean-producer)
    // 外层由本脚本的 BUILD_TIMEOUT 兜住;内层是每条 Lake 阶段前的 ensure 前导(最多 ArchiveFetchBudgetSeconds,
    // 超时降级)+ Lake 命令自身的 DefaultProvisionBudgetSeconds;阶段之间还有非 Lake 工作(模块枚举、delta
    // 规划、材料压缩、序列化),由 SupervisorNonLakeReserveSeconds 具名保留。外层 = 阶段数 × (前导 + Lake)
    // + 保留 = LeanCacheBudgetPolicy.InspectorSupervisorBudgetSeconds,脚本里的字面量由本条钉住相等
    // (#4122 三轮评审:7200 < 21600 → 「相等」不够 → 「3 × 内层」漏掉前导与非 Lake 工作)。
    // 路径以 FindRoot + 字面量内联而不走 SupervisorScriptPath():那是 ScribeTestMapDeriver 认得的
    // declared-input 形状(#4122 pass 2 admission 实测:经 helper 读文件被记为 unknown,SL-003 对
    // fork 点之后新增的 unknown 方法 fail-closed),且把脚本登记为本测试的输入——改脚本即选中本测试。
    [Fact]
    public void LeanProducerHoldBudgetEqualsTheInspectorComposite()
    {
        var source = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "scripts", "report", "report-supervisor.sh"));
        var producerHold = LiteralAssignment(source, "LEAN_PRODUCER_BUILD_TIMEOUT_SECONDS");

        Assert.Equal(
            StrataLint.Cli.LeanCacheBudgetPolicy.InspectorSupervisorBudgetSeconds,
            producerHold);
        Assert.True(
            producerHold
                >= StrataLint.Cli.LeanCacheBudgetPolicy.InspectorSequentialLakePhasesWorstCase
                    * (StrataLint.Cli.LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds
                        + StrataLint.Cli.LeanCacheBudgetPolicy.ArchiveFetchBudgetSeconds)
                    + StrataLint.Cli.LeanCacheBudgetPolicy.SupervisorNonLakeReserveSeconds,
            "the composite must enclose every phase's preamble, Lake budget and the non-Lake reserve");
    }

    // 消费者角色(scribe-consumer / digestion-alignment-consumer)不跑 Lake,#403 的挂死上限 7200 对它们
    // 原样保留——producer 的复合预算不得顺带放宽无关工作负载的挂死检测(#4122 pass 3 architecture 席)。
    // 7200 在此以独立字面量第二次写下(与复审线常数同一手法),防「改脚本让另一条测试绿」。
    [Fact]
    public void ConsumerHangBoundIsUnchangedByTheProducerComposite()
    {
        var source = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "scripts", "report", "report-supervisor.sh"));

        Assert.Equal(7200, LiteralAssignment(source, "CONSUMER_BUILD_TIMEOUT_SECONDS"));
        Assert.Contains("if [[ \"$ROLE\" == \"lean-producer\" ]]", source, StringComparison.Ordinal);
    }

    // 阶段数不是拍的:从 inspect.sh 本身数出来,并证明**乘数**——`"$CACHE_RUN" "$LAKE"` 恰有 2 个调用点,
    // 其中 1 个在 invoke_inspector() 函数体之外(build)、1 个在体内(inspect);invoke_inspector 在定义之外
    // 恰有 2 个调用点(delta 子集、全量回退);最坏顺序执行 = 体外 1 + 体内 1 × 调用 2 = 3。
    // 脚本多一条 Lake 阶段、或多一处 invoke_inspector 调用,本条即红。
    [Fact]
    public void InspectorSequentialLakePhaseCountMatchesTheScript()
    {
        var inspector = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "lean-inspector", "inspect.sh"));
        var lines = inspector.Split('\n');
        var bodyStart = Array.FindIndex(lines, static line => line.StartsWith("invoke_inspector() {", StringComparison.Ordinal));
        Assert.True(bodyStart >= 0, "invoke_inspector() is not defined in inspect.sh");
        var bodyEnd = Array.FindIndex(lines, bodyStart, static line => line == "}");
        Assert.True(bodyEnd > bodyStart, "invoke_inspector() body is not closed by a bare `}`");

        static bool IsLakeSite(string line) => line.Contains("\"$CACHE_RUN\" \"$LAKE\"", StringComparison.Ordinal);
        var lakeSitesInside = lines.Skip(bodyStart).Take(bodyEnd - bodyStart + 1).Count(IsLakeSite);
        var lakeSitesOutside = lines.Take(bodyStart).Count(IsLakeSite) + lines.Skip(bodyEnd + 1).Count(IsLakeSite);
        var inspectorCalls = lines.Where((line, index) => index < bodyStart || index > bodyEnd)
            .Count(static line =>
                line.TrimStart().StartsWith("invoke_inspector ", StringComparison.Ordinal)
                || line.Contains("! invoke_inspector ", StringComparison.Ordinal));

        Assert.Equal(1, lakeSitesOutside);
        Assert.Equal(1, lakeSitesInside);
        Assert.Equal(2, inspectorCalls);
        Assert.Equal(
            StrataLint.Cli.LeanCacheBudgetPolicy.InspectorSequentialLakePhasesWorstCase,
            lakeSitesOutside + lakeSitesInside * inspectorCalls);
    }

    private static int LiteralAssignment(string source, string name)
    {
        var match = System.Text.RegularExpressions.Regex.Match(
            source,
            "^" + System.Text.RegularExpressions.Regex.Escape(name) + @"=(?<value>[0-9]+)\s*(#.*)?$",
            System.Text.RegularExpressions.RegexOptions.Multiline);
        Assert.True(match.Success, $"{name} has no literal assignment in the supervisor script");
        return int.Parse(
            match.Groups["value"].Value,
            System.Globalization.CultureInfo.InvariantCulture);
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
