namespace StrataLint.InstructionContract.Tests;

public sealed class WorktreeRoutingInstructionTests
{
    [Theory]
    [InlineData("CLAUDE.md", "### 6.1", "### 6.2")]
    [InlineData("docs/develop/spec/golden-ledger-repo-spec.md", "**A20 ", "**Participation")]
    public void GoverningRoutingKeepsObservationAndIssueWorkInExistingCheckouts(
        string path, string start, string end)
    {
        var routing = Section(Read(path), start, end);

        foreach (var activity in new[]
        {
            "reading", "search", "statistics", "diff", "commits/PRs/issues",
            "creating/editing GitHub issues",
        })
        {
            Assert.Contains(activity, routing, StringComparison.Ordinal);
        }

        Assert.Contains("main checkout or a suitable existing worktree", routing, StringComparison.Ordinal);
        Assert.Contains("git show <commit>:<path>", routing, StringComparison.Ordinal);
        Assert.Contains("Never switch a shared checkout's branch for reading", routing, StringComparison.Ordinal);
        Assert.Contains("do not require a new worktree", routing, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("CLAUDE.md", "### 6.1", "### 6.2")]
    [InlineData("docs/develop/spec/golden-ledger-repo-spec.md", "**A20 ", "**Participation")]
    public void GoverningRoutingPreservesIsolationForMutationsAndBuildSideEffects(
        string path, string start, string end)
    {
        var routing = Section(Read(path), start, end);

        foreach (var activity in new[]
        {
            "Repository edits", "worktree-mutating tests", "mutation verification",
            "checkout changes", "incompatible builds", "builds with write side effects",
        })
        {
            Assert.Contains(activity, routing, StringComparison.Ordinal);
        }

        Assert.Contains("first reuse a suitable linked worktree", routing, StringComparison.Ordinal);
        Assert.Contains("create one only when isolation is needed", routing, StringComparison.Ordinal);
        Assert.Contains("Builds that write are not read-only", routing, StringComparison.Ordinal);
    }

    [Fact]
    public void ObservationOnlyAnsweringDoesNotForceThinkingFilesOrCompilation()
    {
        var skill = Read("skills/formal-thinking-and-answer/SKILL.md");
        var routing = Section(skill, "## Task routing", "## Conversation contract");

        Assert.Contains("observation-only", routing, StringComparison.Ordinal);
        Assert.Contains("creating/editing GitHub issues", routing, StringComparison.Ordinal);
        Assert.Contains("no thinking files, worktree creation or build", routing, StringComparison.Ordinal);
        Assert.Contains("Keep the assertion record in memory", routing, StringComparison.Ordinal);
        Assert.Contains("do not claim a fresh Lean verification", routing, StringComparison.Ordinal);
        Assert.DoesNotContain("every answer is done inside the repository worktree, as files", skill, StringComparison.Ordinal);
        Assert.Contains("first reuse a suitable linked worktree", Section(skill, "## Worktree", "## Method anchors"), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("skills/codex-formalize/SKILL.md")]
    [InlineData("skills/codex-theory-ingest/SKILL.md")]
    public void EditingSkillsReuseSuitableTreesAndDoNotBuildForInspection(string path)
    {
        var environment = Section(Read(path), "### 0.", "### 1.");

        Assert.Contains("Observation-only", environment, StringComparison.Ordinal);
        Assert.Contains("without creating a worktree or running a build", environment, StringComparison.Ordinal);
        Assert.Contains("first reuse a suitable linked worktree", environment, StringComparison.Ordinal);
        Assert.Contains("create one only when isolation is needed", environment, StringComparison.Ordinal);
        Assert.Contains("registration", environment, StringComparison.Ordinal);
        Assert.Contains("branch", environment, StringComparison.Ordinal);
        Assert.Contains("existing material", environment, StringComparison.Ordinal);
        Assert.DoesNotContain("# If not already in a dispatcher-assigned isolated lane:", environment, StringComparison.Ordinal);
        Assert.DoesNotContain("# If no dispatcher-assigned isolated lane exists:", environment, StringComparison.Ordinal);
    }

    [Fact]
    public void IssueAndHotfixInstructionsDoNotRequireAWorktreeForInvestigation()
    {
        var policy = Read("CLAUDE.md");
        var issue = Section(policy, "### 5.4", "### 5.5");
        var hotfix = Section(policy, "### 5.5", "### 5.6");

        Assert.Contains("仅阅读、调查或创建/编辑 GitHub issue", issue, StringComparison.Ordinal);
        Assert.Contains("不要求新建 worktree", issue, StringComparison.Ordinal);
        Assert.Contains("只读调查按第 6.1 条", hotfix, StringComparison.Ordinal);
        Assert.DoesNotContain("未开 worktree 就写", hotfix, StringComparison.Ordinal);
        Assert.Contains("只读与 issue 操作复用现有检出", policy, StringComparison.Ordinal);
        Assert.Contains("observation-only tasks need no new tree or cache preparation", Section(policy, "**Start with compatible reuse**", "### 8.4"), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("agents/CONTEXT.md")]
    [InlineData("docs/CONTRIBUTING.md")]
    public void CommonEntrancesRouteReadsAndRequireCompatibleReuseForEdits(string path)
    {
        var instructions = Read(path);

        Assert.Contains("creating/editing GitHub issues", instructions, StringComparison.Ordinal);
        Assert.Contains("main checkout or a suitable existing worktree", instructions, StringComparison.Ordinal);
        Assert.Contains("git show <commit>:<path>", instructions, StringComparison.Ordinal);
        Assert.Contains("Never switch a shared checkout's branch for reading", instructions, StringComparison.Ordinal);
        Assert.Contains("first reuse a suitable linked worktree", instructions, StringComparison.Ordinal);
        Assert.Contains("create one only when isolation is needed", instructions, StringComparison.Ordinal);
    }

    [Fact]
    public void ReviewSeatsAllowFetchAndAssignedWorktreeBuildsWithoutChangingHeadOrStatus()
    {
        var instructions = Read("tools/scripts/agent/openproblem/templates/blocks/review-readonly-block.md");

        Assert.Contains("git fetch origin dev", instructions, StringComparison.Ordinal);
        Assert.Contains("Do not merge, rebase, commit, reset, stash or switch branches in this worktree, and do not push", instructions, StringComparison.Ordinal);
        Assert.Contains("Builds and tests may run in the assigned worktree", instructions, StringComparison.Ordinal);
        Assert.Contains("must leave `git status --short` empty", instructions, StringComparison.Ordinal);
        Assert.Contains("`git rev-parse HEAD` equal to the assigned head", instructions, StringComparison.Ordinal);
        Assert.DoesNotContain("Do not fetch", instructions, StringComparison.Ordinal);
        Assert.DoesNotContain("Do not run builds or tests", instructions, StringComparison.Ordinal);
    }

    [Fact]
    public void ReviewSeatsUsePinnedReadsAndAskCallerForAnotherWorktree()
    {
        var instructions = Read("tools/scripts/agent/openproblem/templates/blocks/review-readonly-block.md");

        foreach (var command in new[]
        {
            "git show <commit>:<path>",
            "git grep <pattern> <commit> -- <path>",
            "git diff <base> <head> -- <path>",
        })
        {
            Assert.Contains(command, instructions, StringComparison.Ordinal);
            Assert.True(instructions.IndexOf("git fetch origin dev", StringComparison.Ordinal) <
                instructions.IndexOf(command, StringComparison.Ordinal));
        }

        Assert.Contains("Do not create another worktree", instructions, StringComparison.Ordinal);
        Assert.Contains("including under `/tmp`, `/private/tmp` or `$TMPDIR`", instructions, StringComparison.Ordinal);
        Assert.Contains("If a check needs another worktree, report it to the caller", instructions, StringComparison.Ordinal);
        Assert.Contains("who follows CLAUDE.md §6.1", instructions, StringComparison.Ordinal);
        Assert.DoesNotContain("git worktree add", instructions, StringComparison.Ordinal);
        Assert.DoesNotContain("or create a temporary worktree", instructions, StringComparison.Ordinal);
        Assert.DoesNotContain("Report checks that need writes back to the caller", instructions, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("61-reusable-collaborative-worktrees-and-merged-delivery",
        "### 6.1 Reusable collaborative worktrees and MERGED delivery", 2)]
    [InlineData("3-形式化逃逸内容用途与研究", "## 3. 形式化、逃逸内容、用途与研究", 1)]
    [InlineData("52-工件产地与独立性披露", "### 5.2 工件产地与独立性披露", 1)]
    [InlineData("75-base-判官永久禁令与-sl-030-边界", "### 7.5 base 判官永久禁令与 SL-030 边界", 1)]
    public void ContributingPolicyLinksTargetCurrentHeadings(string anchor, string heading, int count)
    {
        var guide = Read("docs/CONTRIBUTING.md");
        var link = $"../CLAUDE.md#{anchor}";

        Assert.Contains(heading, Read("CLAUDE.md"), StringComparison.Ordinal);
        Assert.Equal(count, guide.Split(link, StringSplitOptions.None).Length - 1);
        Assert.DoesNotContain("#61-独立-worktree-与-merged-完成态", guide, StringComparison.Ordinal);
    }

    private static string Read(string path) =>
        File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path));

    private static string Section(string text, string start, string end)
    {
        var startIndex = text.IndexOf(start, StringComparison.Ordinal);
        Assert.True(startIndex >= 0, $"Missing instruction section: {start}");
        var endIndex = text.IndexOf(end, startIndex + start.Length, StringComparison.Ordinal);
        Assert.True(endIndex >= 0, $"Missing instruction section boundary: {end}");
        return text[startIndex..endIndex];
    }
}
