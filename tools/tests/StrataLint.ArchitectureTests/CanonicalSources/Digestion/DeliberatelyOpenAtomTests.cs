namespace StrataLint.ArchitectureTests;

/// <summary>
/// 有些原子是**蓄意**维持 `residual-open` 的,不是待办。
/// 本类是那句「蓄意」的机器形式 —— 在此之前它只是 `D5/X_Frontier/GovernanceDeferrals.lean`
/// 注释里的一句话,而注释拦不住 `make cover`。
/// </summary>
public sealed class DeliberatelyOpenAtomTests
{
    /// <summary>
    /// `theorem/6.35`(容器原子 `pzg-residual-033694bc…`)必须留在 `residual-open`。
    ///
    /// **为什么**:它的三条 `chain_atoms` 已全部 `absorbed-closed`,故按仓内容器语义,
    /// 对它**再显式 cover 一次**即会通过并使其进入 `absorbed-closed`;没有任何东西拦着。
    /// 而它闭合所依据的三条里有两条是 **#2647 认定的假结账**
    /// (`clause/2` 的「四维多项式映射」、`clause/3` 的「收敛双指数」——
    /// 二者在绑定它们的定理里根本没被 claim)。
    ///
    /// **为什么这道闸必须是机器**:`absorbed-closed` **退不回来** ——
    /// #2647 已逐条读码确认不存在任何 CLI 动词能把原子从 `absorbed-closed` 退回 open/partial,
    /// 隔离区路径对「已有 formalization receipt 的原子」无条件抛出,
    /// 手改 YAML 会被 SL-016 判词拦下。故这是一个**不可逆**动作,按第 20 条应设事前硬门,
    /// 而不是事后检测。在本类之前,「不要 cover 它」只存在于两条注释和知情者的记忆里。
    ///
    /// **本类不是 #2647 要立的那个类**。#2647 要的是「覆盖被证明过强时如何诚实退回」的
    /// 类定义与 canonical writer,那是 τ=0 的裁决(记于 `D5-T0048`),本类不预设它的任何答案,
    /// 也不判任何忠实性 —— 它只保住现状,免得在制度建立之前先把错账坐实。
    ///
    /// **红了怎么办**:不要删本测试,也不要改这里的哈希去迁就新位置。
    /// 先读 `D5/X_Frontier/GovernanceDeferrals.lean` 的 `D5-T0045` / `D5-T0047` / `D5-T0048`
    /// 与 issue #2647 / #2602;若确已建立 correction 语义并有权闭合它,连同本测试一并删除,
    /// 并在 PR 里写明依据的是哪一条已落地的 writer。
    /// </summary>
    [Fact]
    public void Theorem635ContainerRemainsResidualOpen()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "Meta",
            "Digestion",
            "backfill",
            "pzg-v170",
            "residual-open",
            "pzg-residual-033694bc925e4b074b232ff39d6164efb97d1796160c841ed64468ff5b5e282f.yaml");

        Assert.True(
            File.Exists(path),
            "容器原子 theorem/6.35 (pzg-residual-033694bc…) 不再位于 residual-open。"
            + "它是**蓄意**维持 open 的(D5-T0045),因为它闭合所依据的三条 chain atom 中有两条"
            + "是 #2647 认定的假结账,而 absorbed-closed 在本仓**退不回来**(无 canonical writer)。"
            + "若这是一次 make cover 的结果,请撤回该 cover;"
            + "若确已建立 #2647 所要的 correction 语义,请连同本测试一并删除并写明依据。");

        var atom = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "Meta",
            "Digestion",
            "backfill",
            "pzg-v170",
            "residual-open",
            "pzg-residual-033694bc925e4b074b232ff39d6164efb97d1796160c841ed64468ff5b5e282f.yaml"));

        Assert.Contains("ast_path: theorem/6.35", atom, StringComparison.Ordinal);

        Assert.Contains(
            "coverage_gids: []",
            atom,
            StringComparison.Ordinal);
    }
}
