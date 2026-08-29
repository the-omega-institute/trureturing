using StrataLint.Engine;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

// 消化不是 CI 的事(2026-08-19 owner 裁决)。理论卷的消化由本地 `make ingest` 完成,
// CI 只**校验**账本是否闭合(SL-016 在 required 的 admission 检查里),不代跑消化。
//
// 此前的形态是一个 `pull_request_target` workflow:只读 job 产提案 + 最小写 job
// 独立重算后写回 PR 分支。它拖出一整条串行缺陷链(CWD 解析、两层超时预算、
// 事件快照式 strict),而它本要服务的第三方 PR 场景**结构上不可行**——
// `GITHUB_TOKEN` 对 fork 无写权限。整套已删除。
//
// 作用面(不冒领):本守卫只判 `ci.yml`——删除 theory-ingest 后它是仓内**唯一**的
// workflow。若日后新增 workflow,本守卫不会自动覆盖它;但新增 workflow 属 SL-022
// 保护面变更,必经评审,届时须一并扩展此处。不用目录枚举,因为那会让 Scribe
// 测试映射无法静态确定读取面(TestMapUnknownReason.DirectoryEnumeration)。
public sealed class DigestionWorkflowArchitectureTests
{
    [Fact]
    public void NoWorkflowRunsTheDigestionProducerOrWritesBackToAPullRequest()
    {
        // 用 TestRepositoryLayout.ReadAllText + 内联字面量:Scribe 测试映射只认这一形
        // (AddLiteralCreatePath 要求 RepositoryRelativePath.Create 的实参是字符串字面量),
        // 其余写法一律记为 VariablePath 未知债。故此处不用常量、不用 Path.Combine。
        var workflow = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create(".github/workflows/ci.yml"));

        Assert.DoesNotContain("make ingest", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("theory-ingest-closure", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("force-with-lease", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("theory-ingest-bot", workflow, StringComparison.Ordinal);
        // 不断言「不得用 pull_request_target」:ci.yml 本就以它承载 admission 的信任拓扑
        // (workflow 文本取自 base 侧),与消化无关。本守卫判的是「不代跑消化、不写回」,
        // 不是触发器形态。
    }
}
