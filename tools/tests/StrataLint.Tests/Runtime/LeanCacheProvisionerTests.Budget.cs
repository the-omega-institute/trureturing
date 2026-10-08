using StrataLint.Cli;

namespace StrataLint.Tests;

// LeanCacheProvisionerTests 的预算相关片段(7 个测试)。
// 分出来的直接理由是余量:宿主原 798 行,离 SL-003 的 800 行硬线**只剩 2 行**,
// 而它是被频繁改动的缓存供给测试 —— 下一次加任何一行都会当场撞线。
// 私有辅助(WithBudget / AssertCacheGetBudget / WritePins / ReadPins)两半都在用,
// 故留在宿主;partial 类跨文件共享成员。
// [Collection] 特性只在宿主声明一次,片段不重复。

public sealed partial class LeanCacheProvisionerTests
{
    private const string BudgetVariable = "STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS";

    [Fact]
    public void NamedBudgetsShareTheLoadBearingValue()
    {
        var lean = LeanCacheProvisioner.LeanCommandBudget;
        Assert.Equal(PinnedProductionBudgets.LeanCacheProvisionBudget, lean);
        Assert.Equal(lean, LeanCacheProvisioner.DependencyFetchBudget);
    }

    [Fact]
    public void NamedBudgetsFollowTheClampedEnvironmentOverride()
    {
        WithBudget("99999", () =>
        {
            var clamped = PinnedProductionBudgets.LeanCacheProvisionCeiling;
            Assert.Equal(clamped, LeanCacheProvisioner.LeanCommandBudget);
            Assert.Equal(clamped, LeanCacheProvisioner.DependencyFetchBudget);
        });
    }

    /// <summary>
    /// 该值是 `policy-override`,其**取值依据**是覆盖全量冷建并留并发余量。
    ///
    /// 上一版把它判为「域外活性上限」,依据是「对正常路径 766s 有 9.4 倍」——
    /// **那个 766s 是 CI 热态报告生产的耗时,而本值界的是本地 worktree 的 Lake 命令**,
    /// 拿一个环境的读数当了另一个环境的判据。本地三级回退(clonefile → archive →
    /// ReproduceExisting)全落空即全量冷建 **3388s**,比值只有 2.13。
    ///
    /// 故本测试钉的是**本地口径**的那个关系,不再是 CI 口径。
    /// </summary>
    [Fact]
    public void BudgetClearsTheLocalFullColdBuildWithConcurrencyHeadroom()
    {
        // 本地全量冷建实测(2026-08-23,28 核,含并发,EXIT=0,1571 模块)。
        const int LocalFullColdBuildSeconds = 3388;

        // #4120 修订时(2026-08-30)的规模投影:dev `9b629c376` 2672 模块 × 2.156588 s/模块
        // (= 3388/1571,本机上界侧锚点)= ceil(5762.40) = 5763s。这是本值唯一的耗时依据
        // (CI 的检查点种子链不是耗时读数,见 LeanCacheBudgetPolicy 负读数⑤)。首次收口的判据
        // (清过冷建读数的两倍)须对**当前**规模成立,否则复审线被跨过后只改复审线、不改预算,
        // 就是「改数让测试绿」。
        const int ProjectedFullColdBuildSecondsAtRevision = 5763;

        // 负读数①:旧值 1800 对 1656 的 8% 余量被并发吃掉而失败。故须显著多于 1 倍。
        Assert.True(
            LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds
                > LocalFullColdBuildSeconds * 2,
            "预算未清过本地全量冷建的两倍,并发余量不足以避免重演 1800 的失败");
        Assert.True(
            LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds
                > ProjectedFullColdBuildSecondsAtRevision * 2,
            "预算未清过 #4120 修订时规模投影冷建的两倍:复审线到期后预算本身未重新收口");

        // 有限:预算必须封顶,否则挂死检测失效。
        Assert.True(
            LeanCacheBudgetPolicy.MinimumConfigurableBudgetSeconds
                < LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds);
    }

    /// <summary>
    /// `policy-override` 须**报全**:这不是派生值、日期、域、正反读数、永久案号、
    /// owner、退出条件、非永久。报不全即规矩所指的「无源未报」(第四形)。
    ///
    /// 本测试读该常数的声明文本并逐项核对 —— 缺任一项即红,迫使改动者补齐而非静默删注。
    /// </summary>
    [Fact]
    public void PolicyOverrideDeclarationReportsEveryRequiredItem()
    {
        var file = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "StrataLint.Lean", "Lean", "LeanCacheBudgetPolicy.cs"));

        // 只看该常数自己的 <summary> 块(#4122 tests 席:全文件 token 检查会被别处出现的同一
        // 字符串满足,例如复审线常数的注释里也写着案号与日期)。
        var constantIndex = file.IndexOf("internal const int DefaultProvisionBudgetSeconds", StringComparison.Ordinal);
        Assert.True(constantIndex > 0, "DefaultProvisionBudgetSeconds declaration not found");
        var head = file[..constantIndex];
        var summaryStart = head.LastIndexOf("/// <summary>", StringComparison.Ordinal);
        Assert.True(summaryStart >= 0, "DefaultProvisionBudgetSeconds has no <summary> block");
        var declaration = head[summaryStart..];

        // 逐项按**带标签的字段**核对(#4122 tests 席:无标签的 token 出现在块内任何位置都能满足,
        // 那不是钉住修订字段)。每个正则都锚在该项的标签上。
        foreach (var (label, pattern) in new[]
        {
            ("型别", @"\*\*分类:`policy-override`。\*\*"),
            ("非派生", @"「这不是派生值。」"),
            ("修订日期", @"\*\*日期\*\*:2026-08-30"),
            ("首次日期", @"首次收口 2026-08-25"),
            ("修订记录", @"\*\*修订记录\(2026-08-30\)\*\*"),
            ("域", @"\*\*域\*\*:"),
            ("正读数", @"\*\*正读数\*\*:"),
            ("负读数", @"\*\*负读数\*\*:"),
            ("永久案号(首次)", @"\*\*永久案号\*\*:https://github\.com/the-omega-institute/trureturing/issues/2535"),
            ("永久案号(修订)", @"→ https://github\.com/the-omega-institute/trureturing/issues/4120"),
            ("owner", @"\*\*owner\*\*:"),
            ("退出条件", @"\*\*退出条件 / 复审触发\*\*"),
            ("非永久", @"\*\*非永久\*\*:"),
        })
        {
            Assert.True(
                System.Text.RegularExpressions.Regex.IsMatch(declaration, pattern),
                $"policy-override 声明缺项或标签不符:{label}(pattern {pattern})");
        }
    }

    [Fact]
    public void ConfiguredBudgetAppliesToDependencyFetchProcess() =>
        AssertCacheGetBudget("5400", 5400);

    /// <summary>
    /// 旋钮的解析与 clamp:低于下界落到下界,高于上界落到上界(上界 = 声明的 policy-override 值,
    /// 无派生 —— 派生式已于 #3119 删除)。
    /// </summary>
    [Theory]
    [InlineData("1", 300)]
    [InlineData("30000", 21600)]
    public void ConfiguredBudgetUsesInvariantParsingAndClamps(string raw, int expectedSeconds)
    {
        AssertCacheGetBudget(raw, expectedSeconds);
    }

    /// <summary>
    /// 非法旋钮取值应回落到默认路径,而默认路径就是上限本身。
    /// 上一版此处期望「该树的派生值」,现无派生可言。
    /// </summary>
    [Fact]
    public void UnparseableBudgetFallsBackToTheCeiling()
    {
        WithBudget("invalid", () =>
            Assert.Equal(
                PinnedProductionBudgets.LeanCacheProvisionBudget,
                LeanCacheProvisioner.LeanCommandBudget));
    }
}
