using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// 「已入库、尚未消化」是账本四态里的 <c>open</c>,不是违规。它是内容层的、完全可逆的、
/// 随时可由 producer(<c>make ingest</c>)重新检出的状态,故按 CLAUDE.md 第 20 条执法分级
/// 归「允许 + 事后检测 + 快速勘正」,不归事前硬门——一个只改 markdown 的 PR 不该被它挡住,
/// 而第三方本来就跑不了本仓的 producer。
///
/// 为何**一律**非阻断,而非只豁免本次改动碰过的理论卷:窄豁免会在合入后毒化 dev——
/// 同一批未闭合原子对后续每个 PR 都不再豁免,全仓变红(仓内先例:SL-003 曾锁死七个在飞 PR)。
/// 一律非阻断则谁也堵不住,结构上不可能毒化。
///
/// 但**不得静默**:判词仍须发出且带补救命令。绿而无声等于把「未消化」变成不可见,
/// 那才是真的降级(第 20 条红线:允许 open,不允许浮账)。
///
/// **覆盖边界(如实标注)**:本测试只钉住「全新卷、无 source」这一形态。另一形态
/// ——已有卷追加内容、新原子未登记(即 #2403 的实测形态:80 个未登记原子、自带闭合 0)
/// ——的非阻断性**没有单元测试覆盖**:构造该状态需要完整的基线目录账本夹具,数轮尝试
/// 均未使 aligner 产出 residual,成本已超过它能多证明的东西。该形态的依据是代码改动
/// 本身(判词不再进入阻断 Findings,改由消费者按类型赋 Observe)与 #2403 的真实读数,
/// 不是单元测试。留此白比留一个可能空转的绿测试诚实。
/// </summary>
public sealed class UndigestedIsOpenNotBlockingTests
{
    private const string NewVolumePath = "docs/develop/theory/BRAND_NEW.md";
    private const string DeclaredPath = "docs/develop/theory/DECLARED.md";

    // 声明卷含两条定理,账本只登记 9.9 —— 9.10 即「已入库、尚未消化」的残余。
    private static readonly byte[] DeclaredBytes = Encoding.UTF8.GetBytes(
        "# 已声明卷\n\n## 定理 9.9\n\n证。\n\n## 定理 9.10\n\n证。\n");

    private static BackfillInventoryDocument LedgerWithOneRegisteredAtom()
    {
        var declared = GenericAtomizer.Atomize(DeclaredBytes, TheoryAtomizerRules.None);
        Assert.Equal(2, declared.Claims.Length);
        var atom = declared.Claims[0];
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        return DigestionTestSupport.Document(
            AtomizerRegistry.GenericId,
            [
                DigestionTestSupport.Entry(
                    atom,
                    atom.Fingerprints.RawSha256["sha256:".Length..],
                    AtomizerRegistry.GenericId,
                    sourceId: "declared",
                    sourcePath: DeclaredPath,
                    casRef: capture.Reference),
            ],
            "declared",
            DeclaredPath,
            GenreRegistryCheck.Collected([]));
    }

    [Fact]
    public void ABrandNewVolumeWithNoSourceIsReportedWithoutBlocking()
    {
        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));
        var policy = RegistryLoadAssert.Accepted(outcome).Policy;
        var snapshot = DigestionTestSupport.Snapshot(
            (NewVolumePath, Encoding.UTF8.GetBytes("# 全新卷\n\n## 定理 1.1\n\n证。\n")),
            (DeclaredPath, DeclaredBytes));

        var findings = BackfillInventoryRule.EvaluateDocument(
            new BackfillInventoryValidationContext(
                snapshot,
                snapshot,
                policy,
                DigestionTestSupport.AcceptedLean(Array.Empty<string>()),
                null),
            LedgerWithOneRegisteredAtom());

        var missing = Assert.Single(findings, finding => finding.Message.Contains(
            "has no digestion source",
            StringComparison.Ordinal));

        // 仍然报出来,且带补救命令——不允许静默。
        Assert.Contains(NewVolumePath, missing.Message, StringComparison.Ordinal);
        Assert.Contains("make ingest", missing.Message, StringComparison.Ordinal);
        // 但不阻断准入。Effect 为 null 表示继承规则默认(SL-016 默认 Block),
        // 故这里必须是显式的 Observe,null 不算通过。
        Assert.Equal(AdmissionEffect.Observe, missing.Effect);
    }

}
