using StrataLint.Engine;

namespace StrataLint.Tests;

// ①′ 触发载荷(器律⑦″,2026-09-07 立):**正例** —— 本文件故意读本仓真实 workflow,
// 应被 WorkflowTestProhibitionTests.NoTestSourceReadsTheRealWorkflow 判红。
// 用途是让新判据在真实 pull_request_target 事件上被触发一次并产出具名判词;
// 验完即关闭该 PR,载荷不进任何分支。
public sealed class TriggerProbeWorkflowTests
{
    [Fact]
    public void ReadsTheRealWorkflowOnPurpose()
    {
        var path = Path.Combine(TestRepositoryLayout.FindRoot(), ".github/workflows/ci.yml");
        Assert.True(File.Exists(path));
    }
}
