using StrataLint.Engine;

namespace StrataLint.Tests;

// SL-016 的唤醒路径。独立成文件而非并入 RuleEngineTests:后者已达 SL-003 硬线 800 行,
// 按 CLAUDE.md 第 8 条「桶满则裂、只裂不迁」,新条目入新桶,既有条目原地不动。
public sealed class Sl016WakeupTests
{
    // 理论卷改按路径规则治理后,GovernanceDocuments 里已无理论路径。若 IsAffectedBy
    // 仍只靠那张清单,只改理论卷的候选就**整条规则不触发**(RuleCatalog 对未命中的
    // 规则整条跳过),消化账本检测随之失效——实测见 #2462:追加一条可原子化命题、
    // 不跑 make ingest,make gate EXIT=0 放行。此测试钉住该唤醒路径。
    [Fact]
    public void TheoryVolumeChangeWakesSl016EvenThoughItIsNoLongerEnumeratedInTheRegistry()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create(
            ["docs/develop/theory/INTERFACE_PAPER.md"]));

        Assert.DoesNotContain(
            context.Policy.GovernanceDocuments,
            static path => path.Value.StartsWith(
                DigestionOpaquePathPolicy.TheoryRootPath,
                StringComparison.Ordinal));
        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
    }

}
