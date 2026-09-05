using StrataLint.Cli;
using StrataLint.Engine;
using System.Text;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    // Candidate Lean validation is bound only to the candidate tree. The protected base may move
    // a Lean source after the candidate fork without requiring any old-side Lean artifact.
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
        RawLeanReportArtifact.WriteFile(
            candidateReport,
            Decode(Snapshot(fixture.Files)),
            LeanAxiomReport.Create(fixture.Reports));

        var environment = new ProductionCliEnvironment(
            candidate.Path,
            new GitRepositoryGateway(candidate.Path),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            "--protected-base", protectedBase,
            "--candidate-lean-report", candidateReport,
        ]);

        if (outcome is AdmissionOutcome.InfrastructureFailure failure)
        {
            Assert.Fail(
                "check 不得因 dev 在候选在飞期间前进而报基础设施故障。实际: "
                + failure.Message);
        }
    }

    // 「旧侧」有两个不同的语义,#1146 只修好了一个。
    //   保守比较问「候选在扩展哪个受保护状态」→ protected base;
    //   冻结保留性问「候选是否删了它出发时就有的东西」→ **fork point(merge-base)**。
    // 二者被同一个 `baseline` 快照回答,于是 #1146 之后,dev 在候选分叉之后追加的任何
    // 冻结账本证书都会被读成
    // 「候选删除了受保护之物」。
    //
    // 生产实证:PR #1150 撞上
    //   `SL-008 Golden/Frozen/events.jsonl: candidate content-addressed ledger does not
    //    retain protected baseline file byte-for-byte`
    // ——其分支点到 dev tip 之间,`Golden/Frozen/accepted/` 新增 4 个由保守扩展仪式产出的证书。
    // 实测近 60 次 dev 合并中 38 次(63%)追加此类证书,故这是常态而非边角。
    //
    // 本测试直接使用仍现役的 SL-008 冻结事件复现。
    [Fact]
    public void CheckDoesNotBlameTheCandidateForAppendOnlyEntriesAddedToTheProtectedBaseAfterTheFork()
    {
        using var candidate = new TemporaryDirectory();
        using var reports = new TemporaryDirectory();
        var fixture = new RuleFixture();
        var candidateFreeze = FreezeEvent(fixture, RuleFixture.RingPath);
        var devFreeze = FreezeEvent(fixture, RuleFixture.ValuesBindingPath);

        // A —— 分叉点。
        InitializeRepository(candidate.Path);
        WriteFiles(candidate.Path, fixture.Baseline);
        ReviewRegressionTests.RunGit(candidate.Path, "add", ".");
        ReviewRegressionTests.RunGit(candidate.Path, "commit", "-m", "fork point");

        // C —— 候选自 A 分出并冻结一个节点。
        ReviewRegressionTests.RunGit(candidate.Path, "checkout", "-b", "candidate");
        fixture.Files[RuleFixture.BlueprintPath] += "\n";
        fixture.Files[candidateFreeze.Path] = candidateFreeze.Text;
        fixture.Files[candidateFreeze.StatePath] = candidateFreeze.StateText;
        WriteFiles(candidate.Path, fixture.Files);
        ReviewRegressionTests.RunGit(candidate.Path, "add", ".");
        ReviewRegressionTests.RunGit(candidate.Path, "commit", "-m", "candidate ordinary change");

        // B —— dev 在候选在飞期间冻结另一个节点。候选当然没有它。
        ReviewRegressionTests.RunGit(candidate.Path, "checkout", "dev");
        var protectedFiles = new Dictionary<string, string>(fixture.Baseline, StringComparer.Ordinal)
        {
            [devFreeze.Path] = devFreeze.Text,
            [devFreeze.StatePath] = devFreeze.StateText,
        };
        WriteFiles(candidate.Path, protectedFiles);
        ReviewRegressionTests.RunGit(candidate.Path, "add", ".");
        ReviewRegressionTests.RunGit(candidate.Path, "commit", "-m", "dev freezes another node");
        var protectedBase = GitText(candidate.Path, "rev-parse", "HEAD");

        ReviewRegressionTests.RunGit(candidate.Path, "checkout", "candidate");

        var candidateReport = Path.Combine(reports.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(
            candidateReport,
            Decode(Snapshot(fixture.Files)),
            LeanAxiomReport.Create(fixture.Reports));
        var environment = new ProductionCliEnvironment(
            candidate.Path,
            new GitRepositoryGateway(candidate.Path),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            "--protected-base", protectedBase,
            "--candidate-lean-report", candidateReport,
        ]);

        var frozenBlame = outcome is AdmissionOutcome.RuleRejected rejected
            ? rejected.Diagnostics
                .Where(static item => item.RuleId == RuleId.CreateKnown(8))
                .Select(static item => $"{item.RuleId} {item.Path}: {item.Message}")
                .ToArray()
            : [];

        Assert.Empty(frozenBlame);
    }

    private static (string Path, string Text, string StatePath, string StateText) FreezeEvent(
        RuleFixture fixture,
        string descriptorSelector)
    {
        var path = RepoPath.CreateKnown(descriptorSelector);
        var declarations = CanonicalStatementWriter.DeclarationStatementIds(
            path,
            fixture.Reports[descriptorSelector]);
        var material = new FrozenNodeMaterial(
            path,
            declarations,
            StatementId.Create(FrozenContentHash.Compute(
                FrozenHashDomains.Statement,
                CanonicalStatementWriter.WriteModule(path, declarations).AsSpan())),
            FrozenNodeId.Create("sha256:" + new string('0', 64)),
            [],
            []);
        var payload = FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(material));
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent("Freeze", payload);
        return (
            FrozenLedgerChangeClassifier.AcceptedPath(encoded.Hash),
            Encoding.UTF8.GetString(encoded.Bytes.AsSpan()),
            FrozenStatePath.FromModulePath(path).Value,
            Encoding.UTF8.GetString(FrozenStateRecord.Encode(material.StatementId).AsSpan()));
    }

    private static void InitializeRepository(string root)
    {
        ReviewRegressionTests.RunGit(root, "init", "-b", "dev");
        ReviewRegressionTests.RunGit(root, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(root, "config", "user.name", "StrataLint Tests");
    }

    private static void WriteFiles(string root, IReadOnlyDictionary<string, string> files)
    {
        foreach (var (path, text) in files)
        {
            var absolute = Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(absolute)!);
            File.WriteAllText(absolute, text, new UTF8Encoding(false));
        }
    }

    private static string GitText(string root, params string[] arguments) =>
        ReviewRegressionTests.RunGit(root, arguments).Trim();
}
