using System.Text;

namespace StrataLint.InstructionContract.Tests;

public sealed class RepositoryPolicyInstructionTests
{
    [Fact]
    public void FormalizationInstructionsPermitCheckpointHistoryBeforePublication()
    {
        var text = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
            "skills/codex-formalize/SKILL.md"), Encoding.UTF8);

        Assert.DoesNotMatch(@"(?i)remain\s+uncommitted[^.]*Step 7", text);
        Assert.DoesNotMatch(@"(?i)(?:one|single)\s+(?:explicit\s+)?builder(?:-owned)?\s+commit", text);
        Assert.DoesNotMatch(@"(?i)single\s+explicit\s+commit\s+from\s+Step 7", text);
        Assert.Contains("publication base", text, StringComparison.Ordinal);
        Assert.Contains("publication tip", text, StringComparison.Ordinal);
        Assert.Contains("cumulative diff", text, StringComparison.Ordinal);
        Assert.Contains("Do not rewrite published history", text, StringComparison.Ordinal);
    }

    [Fact]
    public void GoverningInstructionsDoNotRequirePublishingEveryLocalCheckpoint()
    {
        var text = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "CLAUDE.md"), Encoding.UTF8);

        Assert.DoesNotContain("提交即推", text, StringComparison.Ordinal);
        Assert.DoesNotContain("及时提交、推送", text, StringComparison.Ordinal);
        Assert.Contains("Local WIP checkpoints may remain unpublished", text, StringComparison.Ordinal);
        Assert.Contains("complete, currently checked source/projection unit", text, StringComparison.Ordinal);
    }

    [Fact]
    public void WorktreeCheckpointInstructionsSeparateSavingFromDelivery()
    {
        var root = TestRepositoryLayout.FindRoot();
        foreach (var path in new[] { "CLAUDE.md", "skills/formal-thinking-and-answer/SKILL.md", "skills/codex-formalize/SKILL.md" })
        {
            var text = File.ReadAllText(Path.Combine(root, path), Encoding.UTF8);
            Assert.Contains("make worktree-checkpoint MESSAGE=FILE", text, StringComparison.Ordinal);
            Assert.Contains("after every recoverable unit", text, StringComparison.Ordinal);
            Assert.Contains("before long checks", text, StringComparison.Ordinal);
            Assert.Contains("before hand-off", text, StringComparison.Ordinal);
            Assert.Contains("before normal end", text, StringComparison.Ordinal);
            Assert.Contains("WIP", text, StringComparison.Ordinal);
            Assert.Contains("saved bytes only", text, StringComparison.Ordinal);
            Assert.Contains("no heartbeat or empty commits", text, StringComparison.Ordinal);
        }
    }

    [Theory]
    [InlineData("CLAUDE.md")]
    [InlineData("skills/formal-thinking-and-answer/SKILL.md")]
    [InlineData("docs/develop/spec/golden-ledger-repo-spec.md")]
    public void WorktreeDeliveryReturnsToBoundedPool(string path)
    {
        var text = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path), Encoding.UTF8);
        Assert.Contains("make worktree-return PR=", text, StringComparison.Ordinal);
        Assert.Contains("WRITERS_JOINED=1", text, StringComparison.Ordinal);
        Assert.Contains("MERGED", text, StringComparison.Ordinal);
        Assert.Contains("make worktree-remove", text, StringComparison.Ordinal);
        Assert.DoesNotContain("the task removes the worktrees it created", text, StringComparison.Ordinal);
        Assert.DoesNotContain("remove a worktree this run created", text, StringComparison.Ordinal);
    }

    [Fact]
    public void PrToolDocumentationNoLongerRequiresCallerPolling()
    {
        var text = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "CLAUDE.md"), Encoding.UTF8);
        Assert.Contains("`pr.sh` 为 `open`/`watch` 双动词", text, StringComparison.Ordinal);
        Assert.Contains("默认 arm auto-merge", text, StringComparison.Ordinal);
        Assert.Contains("`AUTO_MERGE=0` 不 arm 但仍等 CI", text, StringComparison.Ordinal);
        Assert.Contains("`DRAFT=1` 传 `--draft`", text, StringComparison.Ordinal);
        Assert.DoesNotContain("缺省不 arm auto-merge", text, StringComparison.Ordinal);
        Assert.DoesNotContain("create → App-token 隔离 → arm auto-merge → 等 required-CI 判词", text, StringComparison.Ordinal);
        Assert.DoesNotContain("需要重复由调用方 shell 循环", text, StringComparison.Ordinal);
        Assert.DoesNotContain("单动词(`update`", text, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestionDiagramNamesFourStates()
    {
        var text = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "CLAUDE.md"), System.Text.Encoding.UTF8);
        Assert.Contains("\u6d88\u5316\u8d26\u76ee\u00b7\u56db\u6001\u89c1\u4e0b", text, StringComparison.Ordinal);
    }
}
