using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    // 旧侧身份必须唯一。check 用两样东西描述「旧侧」:
    //   (a) prepared.Revision 解出的仓库快照;
    //   (b) --baseline-lean-report 这份工件。
    // CI 从 pull_request.base.sha 的树产出 (b);而 GitRepositoryGateway.Prepare 在
    // protected base 不是候选祖先时把 (a) 换成 merge-base。dev 在候选在飞期间前进
    // 时,二者指向两棵不同的树,同一份 report 被要求同时是两棵树的 report。
    //
    // 这不是故障场景:候选早于 dev 的某次改动分出,是并行开发的常态。
    // 它此前不可达,只因 strict 分支保护强制 merge-base == base.sha;
    // strict 已于 2026-08-10 按 τ=0 裁决永久关闭(CLAUDE.md 第 19 条),
    // 故此形态自那时起是常态,PR #1144 是它的首个实测。
    [Fact]
    public void CheckAcceptsACandidateBranchedBeforeTheProtectedBaseMovedALeanSource()
    {
        using var candidate = new TemporaryDirectory();
        using var reports = new TemporaryDirectory();
        var fixture = new RuleFixture();

        // A —— 候选与 dev 的共同祖先。
        InitializeRepository(candidate.Path);
        WriteFiles(candidate.Path, fixture.Baseline);
        ReviewRegressionTests.RunGit(candidate.Path, "add", ".");
        ReviewRegressionTests.RunGit(candidate.Path, "commit", "-m", "common ancestor");

        // C —— 候选自 A 分出,做一次与 Lean 源无关的普通改动。
        ReviewRegressionTests.RunGit(candidate.Path, "checkout", "-b", "candidate");
        fixture.Files[RuleFixture.BlueprintPath] += "\n";
        WriteFiles(candidate.Path, fixture.Files);
        ReviewRegressionTests.RunGit(candidate.Path, "add", ".");
        ReviewRegressionTests.RunGit(candidate.Path, "commit", "-m", "candidate ordinary change");

        // B —— 候选在飞期间 dev 前进,动了一个 Lean 源文件。B 即 protected base。
        ReviewRegressionTests.RunGit(candidate.Path, "checkout", "dev");
        var protectedFiles = new Dictionary<string, string>(fixture.Baseline, StringComparer.Ordinal)
        {
            [RuleFixture.RingPath] = fixture.Baseline[RuleFixture.RingPath]
                .Replace("def goldenRing : Nat := 0", "def goldenRing : Nat := 1", StringComparison.Ordinal),
        };
        Assert.NotEqual(fixture.Baseline[RuleFixture.RingPath], protectedFiles[RuleFixture.RingPath]);
        WriteFiles(candidate.Path, protectedFiles);
        ReviewRegressionTests.RunGit(candidate.Path, "add", ".");
        ReviewRegressionTests.RunGit(candidate.Path, "commit", "-m", "protected base moves a Lean source");
        var protectedBase = GitText(candidate.Path, "rev-parse", "HEAD");

        // 回到候选:工作树 = C,protected base = B,且 B 不是 C 的祖先。
        ReviewRegressionTests.RunGit(candidate.Path, "checkout", "candidate");
        Assert.NotEqual(protectedBase, GitText(candidate.Path, "merge-base", protectedBase, "HEAD"));

        var candidateReport = Path.Combine(reports.Path, "candidate.json");
        var baselineReport = Path.Combine(reports.Path, "baseline.json");
        File.WriteAllBytes(
            candidateReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(fixture.Files)),
                LeanAxiomReport.Create(fixture.Reports)).AsSpan());

        // CI 就是这样产 baseline report 的:从 pull_request.base.sha 的树,即 B。
        File.WriteAllBytes(
            baselineReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(protectedFiles)),
                LeanAxiomReport.Create(fixture.BaselineReports)).AsSpan());

        var environment = new ProductionCliEnvironment(
            candidate.Path,
            new GitRepositoryGateway(candidate.Path),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            "--protected-base", protectedBase,
            "--candidate-lean-report", candidateReport,
            "--baseline-lean-report", baselineReport,
        ]);

        if (outcome is AdmissionOutcome.InfrastructureFailure failure)
        {
            Assert.Fail(
                "旧侧身份不唯一:快照与 baseline Lean report 取自两棵不同的树。"
                + " check 不得因 dev 在候选在飞期间前进而报基础设施故障。实际: "
                + failure.Message);
        }
    }

    // 「旧侧」有两个不同的语义,#1146 只修好了一个。
    //   保守/Lean 配对问「候选在扩展哪个受保护状态」→ protected base(#1146 已改对);
    //   append-only 保留性问「候选是否删了它出发时就有的东西」→ **fork point(merge-base)**。
    // 二者被同一个 `baseline` 快照回答,于是 #1146 之后,dev 在候选分叉之后追加的任何
    // append-only 条目(Chronicle、尸检、冻结账本证书、Digestion CAS)都会被读成
    // 「候选删除了受保护之物」。
    //
    // 生产实证:PR #1150 撞上
    //   `SL-008 Golden/Frozen/events.jsonl: candidate content-addressed ledger does not
    //    retain protected baseline file byte-for-byte`
    // ——其分支点到 dev tip 之间,`Golden/Frozen/accepted/` 新增 4 个由保守扩展仪式产出的证书。
    // 实测近 60 次 dev 合并中 38 次(63%)追加此类证书,故这是常态而非边角。
    //
    // 本测试取 Chronicle 作最小复现(同一缺陷类,装置最简)。
    [Fact]
    public void CheckDoesNotBlameTheCandidateForAppendOnlyEntriesAddedToTheProtectedBaseAfterTheFork()
    {
        using var candidate = new TemporaryDirectory();
        using var reports = new TemporaryDirectory();
        var fixture = new RuleFixture();
        const string forkChronicle = "Chronicle/2026/08/10-fork-point.md";
        const string devChronicle = "Chronicle/2026/08/11-dev-appended-after-the-fork.md";
        fixture.Baseline[forkChronicle] = "# fork point entry\n";
        fixture.Files[forkChronicle] = fixture.Baseline[forkChronicle];

        // A —— 分叉点。
        InitializeRepository(candidate.Path);
        WriteFiles(candidate.Path, fixture.Baseline);
        ReviewRegressionTests.RunGit(candidate.Path, "add", ".");
        ReviewRegressionTests.RunGit(candidate.Path, "commit", "-m", "fork point");

        // C —— 候选自 A 分出,完整保留了分叉点的全部 append-only 条目。
        ReviewRegressionTests.RunGit(candidate.Path, "checkout", "-b", "candidate");
        fixture.Files[RuleFixture.BlueprintPath] += "\n";
        WriteFiles(candidate.Path, fixture.Files);
        ReviewRegressionTests.RunGit(candidate.Path, "add", ".");
        ReviewRegressionTests.RunGit(candidate.Path, "commit", "-m", "candidate ordinary change");

        // B —— dev 在候选在飞期间追加了一条 Chronicle。候选当然没有它。
        ReviewRegressionTests.RunGit(candidate.Path, "checkout", "dev");
        var protectedFiles = new Dictionary<string, string>(fixture.Baseline, StringComparer.Ordinal)
        {
            [devChronicle] = "# appended on dev while the candidate was in flight\n",
        };
        WriteFiles(candidate.Path, protectedFiles);
        ReviewRegressionTests.RunGit(candidate.Path, "add", ".");
        ReviewRegressionTests.RunGit(candidate.Path, "commit", "-m", "dev appends a Chronicle entry");
        var protectedBase = GitText(candidate.Path, "rev-parse", "HEAD");

        ReviewRegressionTests.RunGit(candidate.Path, "checkout", "candidate");

        var candidateReport = Path.Combine(reports.Path, "candidate.json");
        var baselineReport = Path.Combine(reports.Path, "baseline.json");
        File.WriteAllBytes(
            candidateReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(fixture.Files)),
                LeanAxiomReport.Create(fixture.Reports)).AsSpan());
        File.WriteAllBytes(
            baselineReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(protectedFiles)),
                LeanAxiomReport.Create(fixture.BaselineReports)).AsSpan());

        var environment = new ProductionCliEnvironment(
            candidate.Path,
            new GitRepositoryGateway(candidate.Path),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            "--protected-base", protectedBase,
            "--candidate-lean-report", candidateReport,
            "--baseline-lean-report", baselineReport,
        ]);

        var appendOnlyBlame = outcome is AdmissionOutcome.RuleRejected rejected
            ? rejected.Diagnostics
                .Where(static item => item.Message.Contains("append-only", StringComparison.Ordinal))
                .Select(static item => $"{item.RuleId} {item.Path}: {item.Message}")
                .ToArray()
            : [];

        Assert.Empty(appendOnlyBlame);
    }
}
