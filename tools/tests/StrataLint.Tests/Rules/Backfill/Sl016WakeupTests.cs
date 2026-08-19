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

    // IsOpaque 名出三类输入,其改动都能移动原子投影。理论那一类由上面钉住;CAS 那一类
    // 此前无钉子,而「唯一析取项静默失配」正是本文件刚发生过的事故(#2459 清空
    // governance_documents 后,理论卷那一路无声失效)。同形状,同钉法。
    //
    // 第三类 `Meta/Digestion/atomizers.toml` **不在此处钉**:它同时被 governance_documents
    // 命中,故删掉 IsAffectedBy 里那条专用析取项也不会让任何测试变红(已实测)。
    // 那条析取项因此是双保险而非死代码——一旦该文件像理论卷那样被移出清单,它就是
    // 唯一的退路。要钉住它需要一份不含该条目的 registry 夹具,另行处理,不在此假装已钉。
    [Fact]
    public void ContentAddressedAtomChangeWakesSl016()
    {
        const string path =
            "Meta/Digestion/atoms/sha256/0000000000000000000000000000000000000000000000000000000000000000";
        Assert.True(
            DigestionOpaquePathPolicy.IsOpaque(RepoPath.CreateKnown(path)),
            $"{path} is expected to be an opaque digestion input");

        var fixture = new RuleFixture();

        Assert.True(BackfillInventoryRule.IsAffectedBy(fixture.Build(RawChangeSet.Create([path]))));
    }

}
