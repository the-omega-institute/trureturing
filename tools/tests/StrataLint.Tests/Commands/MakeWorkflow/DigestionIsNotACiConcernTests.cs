namespace StrataLint.Tests;

// 消化不是 CI 的事(2026-08-19 owner 裁决)。理论卷的消化由本地 `make ingest` 完成,
// CI 只**校验**账本是否闭合(SL-016 在 required 的 admission 检查里),不代跑消化。
//
// 此前的形态是一个 `pull_request_target` workflow:只读 job 产提案 + 最小写 job
// 独立重算后写回 PR 分支。它的存在拖出一整条串行缺陷链(CWD 解析、两层超时预算、
// 事件快照式 strict),而它本要服务的第三方 PR 场景**结构上不可行**——
// `GITHUB_TOKEN` 对 fork 无写权限。整套已删除。
//
// 本测试钉住「不再长回来」:任何 workflow 都不得代跑消化 producer。
public sealed class DigestionIsNotACiConcernTests
{
    [Fact]
    public void NoWorkflowRunsTheDigestionProducer()
    {
        var workflows = Directory.GetFiles(
            Path.Combine(TestRepositoryLayout.FindRoot(), ".github", "workflows"),
            "*.yml");
        Assert.NotEmpty(workflows);

        var offenders = workflows
            .Where(static path =>
            {
                var text = File.ReadAllText(path);
                return text.Contains("make ingest", StringComparison.Ordinal)
                    || text.Contains("-- ingest", StringComparison.Ordinal)
                    || text.Contains("theory-ingest-closure", StringComparison.Ordinal);
            })
            .Select(Path.GetFileName)
            .ToArray();

        Assert.Empty(offenders);
    }

    [Fact]
    public void NoWorkflowWritesBackToAPullRequestBranch()
    {
        var workflows = Directory.GetFiles(
            Path.Combine(TestRepositoryLayout.FindRoot(), ".github", "workflows"),
            "*.yml");

        var offenders = workflows
            .Where(static path =>
            {
                var text = File.ReadAllText(path);
                return text.Contains("force-with-lease", StringComparison.Ordinal)
                    || text.Contains("theory-ingest-bot", StringComparison.Ordinal);
            })
            .Select(Path.GetFileName)
            .ToArray();

        Assert.Empty(offenders);
    }
}
