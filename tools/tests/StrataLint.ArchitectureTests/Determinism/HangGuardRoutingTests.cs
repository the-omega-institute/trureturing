namespace StrataLint.ArchitectureTests;

/// <summary>
/// hang-guard 预算的声明写着「never bears a test verdict」,但那只是**声明** ——
/// 只有当调用点走 <c>TestProcessRunner</c> 时,超时才会变成 `SkipException`;
/// 走 <c>BoundedProcessRunner</c> 时它抛 `TimeoutException`,于是**恰好承担了判词**(#3670)。
/// </summary>
public sealed class HangGuardRoutingTests
{
    /// <summary>
    /// 判据与其**已知反例集合**都写在
    /// <c>ScribeTestMapDeriver.FindUnroutedHangGuardCalls</c> 的注释里,包括一条诚实交代:
    /// 本判据的 repository read **对映射器不可归因**,它当前可达的理由是
    /// `IsFullSurface` 把 `tools/` 下任何改动转 Full,**不是**归因成立。
    /// </summary>
    [Fact]
    public void EveryHangGuardBudgetGoesThroughTheSkipClassifyingRunner()
    {
        var offenders = ScribeTestMapDeriver.FindUnroutedHangGuardCalls(RepositoryLayout.FindRoot());

        Assert.True(
            offenders.Count == 0,
            "以下调用点把 hang-guard 预算传给了 BoundedProcessRunner.Run,超时会变成 TimeoutException "
            + "(测试失败)而不是 SkipException(基础设施跳过),与该预算「never bears a test verdict」"
            + "的声明相反:"
            + string.Join(", ", offenders)
            + "。改走 TestProcessRunner.Run 即可 —— 它是同签名包装。"
            + "若某处**故意**要 TimeoutException(测超时行为本身),请改用 TestBudgets.ZeroDuration。");
    }
}
