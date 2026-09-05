using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

// SL-030 —— 判官面不得物化非 HEAD 修订的文件(CLAUDE.md 第 19 条 base 判官永久禁止的机器投影)。
// 这些是对合成文本的规则判词测试,不断言本仓真实 workflow 的内容(器律⑦′ 的豁免类:
// 被测对象是消费 workflow/脚本文本的生产逻辑,删掉真实 workflow 后测试仍有意义)。
public sealed class JudgeSurfaceRevisionRuleTests
{
    private const string ScriptPath = "tools/scripts/workflow/gate-helper.sh";
    private const string HarnessGatePath = RuleFixture.HarnessGatePath;
    private const string WorkflowPath = RuleFixture.WorkflowPath;

    [Fact]
    public void WorktreeAddOnTheJudgeSurfaceIsRejected()
    {
        var findings = Evaluate(HarnessGatePath, "git -C candidate worktree add --detach \"$root\" \"$ENGINEERING_BASE\"\n");
        var finding = Assert.Single(findings);
        Assert.Equal(HarnessGatePath, finding.Path);
        Assert.Contains("worktree add", finding.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("git -C candidate show \"HEAD^1:tools/scripts/workflow/floor.py\" > \"$RUNNER_TEMP/floor.py\"")]
    [InlineData("git -C candidate show \"HEAD^1:${CLASSIFIER_PATH}\" > \"$classifier\"")]
    [InlineData("workflow_address=\"$(git -C candidate show \"${workflow_ref}:.github/workflows/ci.yml\" | sha256sum)\"")]
    [InlineData("git show origin/dev:Meta/FILEMAP.toml > policy.toml")]
    [InlineData("git show 3a2a11e34b:tools/x.sh | bash")]
    [InlineData("git cat-file -p \"$BASE:$path\" > \"$path\"")]
    [InlineData("git cat-file -p \"$oid\" > out")]
    [InlineData("git cat-file -p HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git cat-file blob \"$oid\" > script.sh")]
    [InlineData("git cat-file tree \"$tree\"")]
    [InlineData("git cat-file --batch < requests")]
    [InlineData("git cat-file --batch-check < in")]
    [InlineData("git -C \"$ROOT\" archive --format=tar \"$base_sha\" | tar -xf - -C \"$BASE_TREE\"")]
    [InlineData("git archive HEAD^1 | tar -x")]
    [InlineData("git archive -o base.tar HEAD^1")]
    [InlineData("git worktree add --detach /tmp/h \"$ENGINEERING_BASE\"")]
    [InlineData("git worktree add /tmp/h origin/dev")]
    [InlineData("git checkout HEAD^1 -- tools/scripts/workflow/gate.sh")]
    [InlineData("git checkout \"$DEV_BASELINE_SHA\"")]
    [InlineData("git checkout -B lane/x origin/dev")]
    [InlineData("git restore --source=origin/dev tools/scripts/workflow/gate.sh")]
    [InlineData("git read-tree -u HEAD^1")]
    [InlineData("git read-tree -u \"$BASE\"")]
    [InlineData("git checkout-index -a --prefix=base/")]
    [InlineData("git worktree add --detach --lock --reason HEAD /tmp/h \"$BASE\"")]
    [InlineData("git worktree add --frobnicate /tmp/h")]
    [InlineData("git cat-file -p \"$BASE:tools/scripts/workflow/x.sh\" > out # -e only checks existence")]
    [InlineData("git cat-file blob \"$oid\" > -e")]
    [InlineData("git cat-file --textconv HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git read-tree --frob HEAD")]
    [InlineData("git cat-file -p HEAD^{/derive}")]
    [InlineData("git --git-dir \"$dir\" cat-file -p \"$oid\"")]
    [InlineData("git -c core.quotepath=false show HEAD^1:tools/scripts/workflow/x.sh > x.sh")]
    [InlineData("git --work-tree \"$tree\" --git-dir \"$dir\" checkout \"$BASE\" -- tools/scripts/workflow/x.sh")]
    [InlineData("git worktree add --detach /tmp/h 2>/tmp/h.log HEAD^1")]
    [InlineData("git show >out HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git archive --prefix \"release HEAD\" HEAD^1 > base.tar")]
    [InlineData("git archive --add-file HEAD HEAD^1 >out.tar")]
    [InlineData("git restore -sHEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git restore --source=HEAD --source=HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git -C \"/tmp/review repo\" show HEAD^1:tools/scripts/workflow/x.sh > out")]
    [InlineData("git cat-file -e \"$(git show HEAD^1:tools/scripts/workflow/x.sh > out; printf HEAD)\"")]
    [InlineData("git 'show' HEAD^1:tools/scripts/workflow/x.sh > out")]
    [InlineData("git --git-dir \"/tmp/base repo/.git\" show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git --frobnicate show HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git checkout --frob HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("/usr/bin/git show HEAD^1:tools/scripts/workflow/x.sh > out")]
    [InlineData("x=`git show HEAD^1:tools/scripts/workflow/x.sh`")]
    [InlineData("git show HEAD^1:tools/scripts/workflow/x.sh#frag > out")]
    [InlineData("git worktree add /tmp/h $BASE # HEAD")]
    [InlineData("x=\"`git show HEAD^1:tools/scripts/workflow/x.sh >out`\"")]
    [InlineData("x=\"$(printf '%s' ')'; git show HEAD^1:tools/scripts/workflow/x.sh >out)\"")]
    [InlineData("{ git show HEAD^1:tools/scripts/workflow/x.sh >out; }")]
    [InlineData("( git show HEAD^1:tools/scripts/workflow/x.sh >out )")]
    [InlineData("git archive -- HEAD^1 > t.tar")]
    [InlineData("git archive -o/dev/null HEAD^1")]
    [InlineData("git checkout -blane/x origin/dev")]
    [InlineData("x=\"$(y=\"$(git show HEAD^1:tools/scripts/workflow/x.sh)\"; printf %s \"$y\")\"")]
    [InlineData("git worktree add -d '>' HEAD^1")]
    [InlineData("git restore -WsHEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git cat-file --path -e --filters HEAD^1:tools/scripts/workflow/x.sh >out")]
    [InlineData("git show HEAD^1:tools/scripts/workflow/x.sh -- docs")]
    [InlineData("X=1 git show HEAD^1:tools/scripts/workflow/x.sh >out")]
    [InlineData("! git show HEAD^1:tools/scripts/workflow/x.sh >out")]
    [InlineData("cat <(git show HEAD^1:tools/scripts/workflow/x.sh >out)")]
    [InlineData("git worktree add -- -tmp HEAD^1")]
    public void MaterializingAnotherRevisionIsRejected(string line)
    {
        var finding = Assert.Single(Evaluate(ScriptPath, line + "\n"));
        Assert.Equal(ScriptPath, finding.Path);
    }

    [Theory]
    [InlineData("git show \"HEAD:$p\" > \"$p\"")]
    [InlineData("commit_epoch=\"$(git show -s --format=%ct HEAD)\"")]
    [InlineData("source_tree=\"$(git cat-file -p HEAD | sed -n 's/^tree //p')\"")]
    [InlineData("git cat-file -e \"$sha^{commit}\"")]
    [InlineData("git cat-file -e \"${BASE}:${MODULE_PATH}\"")]
    [InlineData("git cat-file -t \"$oid\"")]
    [InlineData("git cat-file -s \"$oid\"")]
    [InlineData("git cat-file blob HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git cat-file -p HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git cat-file -p HEAD^{tree}")]
    [InlineData("git archive --format=tar HEAD -- tools docs | tar -x")]
    [InlineData("git checkout -- tools/scripts/workflow/gate.sh")]
    [InlineData("git checkout -b lane/x")]
    [InlineData("git restore tools/scripts/workflow/gate.sh")]
    [InlineData("git restore --source=HEAD tools/scripts/workflow/gate.sh")]
    [InlineData("git restore -s HEAD tools/scripts/workflow/gate.sh")]
    [InlineData("git worktree add --detach /tmp/h HEAD")]
    [InlineData("git worktree add -b lane/x /tmp/h")]
    [InlineData("git worktree add /tmp/h")]
    [InlineData("git read-tree HEAD")]
    [InlineData("git read-tree -m HEAD^{tree}")]
    [InlineData("base_sha=\"$(git -C candidate rev-parse HEAD^1)\"")]
    [InlineData("workflow_address=\"$(git -C candidate rev-parse \"${workflow_ref}:.github/workflows/ci.yml\")\"")]
    [InlineData("git diff --name-only -z --no-renames HEAD^1 HEAD")]
    [InlineData("git worktree remove --force \"$root\"")]
    [InlineData("git worktree list --porcelain")]
    [InlineData("# git worktree add is forbidden here; see SL-030")]
    [InlineData("git worktree add --quiet --detach /tmp/h HEAD")]
    [InlineData("git worktree add --detach /tmp/h > log")]
    [InlineData("git worktree add --reason \"lane\" --lock /tmp/h")]
    [InlineData("git read-tree HEAD > log")]
    [InlineData("git cat-file -p HEAD:tools/scripts/workflow/x.sh > out # trailing")]
    [InlineData("git cat-file -p HEAD^{commit}")]
    [InlineData("git --no-pager show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git commit -q -m \"archive HEAD^1 notes\"")]
    [InlineData("obj=\"$(git cat-file -p HEAD)\"")]
    [InlineData("git -C \"/tmp/review repo\" show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("git worktree add --detach /tmp/h 2>/tmp/h.log HEAD")]
    [InlineData("git restore -sHEAD -- tools/scripts/workflow/x.sh")]
    [InlineData("git archive --prefix \"release HEAD\" HEAD > base.tar")]
    [InlineData("echo \"$(git rev-parse HEAD^1)\"")]
    [InlineData("git cat-file -p HEAD>out")]
    [InlineData("git worktree add -d /tmp/h HEAD")]
    [InlineData("git read-tree --prefix x/ HEAD")]
    [InlineData("git show HEAD^1 -- tools/scripts/workflow/x.sh")]
    [InlineData("git show HEAD:tools/scripts/workflow/x.sh 2>&1 | tee log")]
    [InlineData("git show HEAD:tools/scripts/workflow/x.sh # HEAD^1:tools/scripts/workflow/y.sh")]
    [InlineData("git worktree add /tmp/h # \"$BASE\"")]
    [InlineData("git archive -- HEAD >/dev/null")]
    [InlineData("git archive -o/dev/null HEAD")]
    [InlineData("git checkout -blane/x")]
    [InlineData("{ git show HEAD:tools/scripts/workflow/x.sh; }")]
    [InlineData("( git rev-parse HEAD^1 )")]
    [InlineData("printf '%s' '{ git show HEAD^1:x }'")]
    [InlineData("git worktree add -d '>' HEAD")]
    [InlineData("git restore -WsHEAD -- tools/scripts/workflow/x.sh")]
    [InlineData("git show HEAD -- docs:notes")]
    [InlineData("git cat-file --path x -e HEAD^1:tools/scripts/workflow/x.sh")]
    [InlineData("git worktree add -- -tmp HEAD")]
    [InlineData("X=1 git rev-parse HEAD^1")]
    [InlineData("cat <(git show HEAD:tools/scripts/workflow/x.sh)")]
    public void ReadingHeadOrMetadataIsAllowed(string line)
    {
        Assert.Empty(Evaluate(ScriptPath, line + "\n"));
    }

    [Fact]
    public void EveryOffendingLineIsReportedWithItsLineNumber()
    {
        var text = "set -euo pipefail\ngit worktree add /tmp/base \"$BASE\"\necho ok\ngit show HEAD^1:tools/x.sh > x.sh\n";
        var findings = Evaluate(ScriptPath, text);
        Assert.Equal(2, findings.Length);
        Assert.Contains(findings, finding => finding.Message.Contains("line 2", StringComparison.Ordinal));
        Assert.Contains(findings, finding => finding.Message.Contains("line 4", StringComparison.Ordinal));
    }

    [Fact]
    public void GitInvocationInsideATrailingCommentIsNotACommand()
    {
        // The lexer sees quotes, so an unquoted word-initial `#` is a real shell comment; nothing
        // after it executes. (The earlier whitespace tokenizer reported this line fail-closed.)
        Assert.Empty(Evaluate(ScriptPath, "echo ok # git show HEAD^1:tools/scripts/workflow/x.sh\n"));
    }

    [Fact]
    public void CrLfTerminatedWorktreeAddIsRejected()
    {
        var finding = Assert.Single(Evaluate(ScriptPath, "git worktree add /tmp/h \"$BASE\"\r\n"));
        Assert.Contains("$BASE", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BackslashContinuationIsOneCommandReportedAtItsFirstLine()
    {
        var finding = Assert.Single(
            Evaluate(ScriptPath, "git \\\n  show HEAD^1:tools/scripts/workflow/x.sh > out\n"));
        Assert.Contains("line 1", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CompositeActionYamlIsOnTheJudgeSurfaceToo()
    {
        const string action = "runs:\n  steps:\n    - uses: actions/checkout@v4\n      with:\n        ref: ${{ github.event.pull_request.base.sha }}\n    - run: git show HEAD^1:tools/scripts/workflow/x.sh > out\n";
        var findings = Evaluate(".github/actions/probe/action.yml", action);
        Assert.Equal(2, findings.Length);
    }

    [Theory]
    [InlineData("      - run: git show HEAD^1:tools/scripts/workflow/x.sh > out")]
    [InlineData("        run: git worktree add /tmp/h \"$BASE\"")]
    [InlineData("      - run: \"git cat-file -p $oid\"")]
    public void WorkflowRunScalarsAreShell(string line)
    {
        var finding = Assert.Single(Evaluate(WorkflowPath, line + "\n"));
        Assert.Equal(WorkflowPath, finding.Path);
    }

    [Theory]
    [InlineData("      - run: |")]
    [InlineData("        run: git rev-parse HEAD^1")]
    [InlineData("      - name: show HEAD^1:tools/scripts/workflow/x.sh in a step name")]
    [InlineData("          git show HEAD:tools/scripts/workflow/x.sh")]
    [InlineData("      # ref: ${{ github.base_ref }} — a comment, not a checkout")]
    public void WorkflowLinesWithoutAMaterializationAreAllowed(string line)
    {
        Assert.Empty(Evaluate(WorkflowPath, line + "\n"));
    }

    [Fact]
    public void NestingDeeperThanTheLexerBoundIsFailClosed()
    {
        var nested = string.Concat(Enumerable.Repeat("$(", JudgeSurfaceShellLexer.MaximumDepth + 2))
            + "git rev-parse HEAD"
            + string.Concat(Enumerable.Repeat(")", JudgeSurfaceShellLexer.MaximumDepth + 2));
        var finding = Assert.Single(Evaluate(ScriptPath, "x=" + nested + "\n"));
        Assert.Contains("nesting deeper", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckingOutTheBaseRefInAWorkflowIsRejected()
    {
        const string workflow = "steps:\n  - uses: actions/checkout@v4\n    with:\n      ref: ${{ github.event.pull_request.base.sha }}\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Equal(WorkflowPath, finding.Path);
    }

    [Fact]
    public void InlineWorkflowBaseRefIsRejected()
    {
        const string workflow = "steps:\n  - with: { ref: ${{ github.base_ref }} }\n";
        var finding = Assert.Single(Evaluate(WorkflowPath, workflow));
        Assert.Equal(WorkflowPath, finding.Path);
        Assert.Contains("a `ref:` naming the protected base", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckingOutTheMergeRefInAWorkflowIsAllowed()
    {
        const string workflow = "steps:\n  - uses: actions/checkout@v4\n    with: { ref: \"${{ github.event_name == 'pull_request_target' && format('refs/pull/{0}/merge', github.event.pull_request.number) || github.sha }}\", fetch-depth: 0 }\n";
        Assert.Empty(Evaluate(WorkflowPath, workflow));
    }

    [Theory]
    [InlineData("tools/scripts/ingest.sh")]
    [InlineData("tools/scripts/agent/scope-freeze-delta.sh")]
    [InlineData("docs/develop/notes/base-judge.md")]
    public void PathsOutsideTheJudgeSurfaceAreNotEvaluated(string path)
    {
        Assert.Empty(Evaluate(path, "git worktree add /tmp/base \"$BASE\"\n"));
    }

    [Fact]
    public void UnchangedJudgeSurfaceFilesAreOutsideTheCandidateDelta()
    {
        var fixture = new RuleFixture();
        fixture.Changes.Clear();
        fixture.Baseline[ScriptPath] = "git worktree add /tmp/base \"$BASE\"\n";
        fixture.Files[ScriptPath] = fixture.Baseline[ScriptPath];
        fixture.Changes.Add(RuleFixture.BlueprintPath);

        Assert.Empty(Diagnostics(fixture.BuildScopeProbe(RawChangeSet.Create(fixture.Changes))));
    }

    [Fact]
    public void RuleIsRegisteredAsABlockingTrustRule()
    {
        var descriptor = Assert.Single(
            RuleCatalog.Default.Descriptors,
            item => item.Id == RuleId.CreateKnown(30));
        Assert.Equal(AdmissionEffect.Block, descriptor.AdmissionEffect);
        Assert.Equal("trust", descriptor.Category);
        Assert.Equal(RuleLifecycle.Active, descriptor.Lifecycle);
    }

    private static ImmutableArray<RuleFinding> Evaluate(string path, string text)
    {
        var fixture = new RuleFixture();
        fixture.Changes.Clear();
        fixture.Files[path] = text;
        fixture.Changes.Add(path);
        return Diagnostics(fixture.BuildScopeProbe(RawChangeSet.Create(fixture.Changes)));
    }

    private static ImmutableArray<RuleFinding> Diagnostics(RuleEvaluationContext context) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(30), context).Diagnostics
            .Select(static diagnostic => new RuleFinding(diagnostic.Path, diagnostic.Message))
            .ToImmutableArray();
}
