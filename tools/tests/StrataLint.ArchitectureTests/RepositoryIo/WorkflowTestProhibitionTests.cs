using System.Text.RegularExpressions;

namespace StrataLint.ArchitectureTests;

/// <summary>
/// 永久禁令(用户 2026-08-29 定,CLAUDE.md 器律⑦′):**不得对 GitHub Actions workflow 写测试。**
///
/// **为什么**:workflow 测试只能校验 workflow 文本**长什么样**,校验不了它**会不会执行**,
/// 故它给出的绿是假绿。本仓两条实测判例:
/// ① 给 `Strip checkout remote state` 加一行 `if: false`,四处覆盖 + 11 条契约 + YAML
///    结构派生的整套机器,**16 个测试全过**(`compile_errors=0`);
/// ② PR #2337 改 workflow,本地 `make preflight` 退出 0 被当成预证绿,合入后连挖五条缺陷,
///    其中 `filemap-conform` 依赖进程 CWD 那条**只能由真跑暴露**。
/// 唯一有效的 workflow 验证是让它在真实事件上跑一次(CLAUDE.md 器律⑦),那是 CI 的活,
/// 不是单元测试的活。形状测试付的是每次改动的税,买到的是零信息。
///
/// **作用面**:`tools/tests/**` 下的 C# 源码不得引用 `.github/workflows` 路径。
///
/// **诚实边界(这是形状扫描,不是完备保证)**——反例集合两维:
/// ① 绕过检查:字符串拼接、变量路径、从文件或环境变量读路径、非 C# 载体(shell/python
///    测试脚本读 workflow)、相对路径 `../.github/workflows`;
/// ② 检查被跳过:本项目不编译或不跑、本 `[Fact]` 被删、扫描前缀写错导致零命中。
/// 故本条只作**早反馈**,不得声称「保证不存在 workflow 测试」。零命中断言由
/// <see cref="ScanSelectsTheTestTreeAndNotTheProhibitionItself"/> 钉住,防止前缀写错而恒绿。
/// </summary>
public sealed class WorkflowTestProhibitionTests
{
    private const string TestTreePrefix = "tools/tests";

    /// <summary>本文件自己必须写出被禁的字面量才能匹配它,故是必然豁免。</summary>
    private const string SelfPath =
        "tools/tests/StrataLint.ArchitectureTests/RepositoryIo/WorkflowTestProhibitionTests.cs";

    /// <summary>
    /// 具名豁免,**removal-only**:新增一项必须先自行论证,不得靠扩充本集合让新的 workflow
    /// 测试通过。豁免的判据只有一条——**被测对象是消费 workflow 的生产逻辑,而不是 workflow
    /// 本身**;这类测试即使删掉 workflow 也仍有意义,故不属本禁令射程。
    /// </summary>
    private static readonly IReadOnlyDictionary<string, string> ProductionConsumerExemptions =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["tools/tests/StrataLint.Tests/Admission/ReviewRegressionTests.Helpers.cs"] =
                "在夹具仓内合成一份 workflow 喂 AdmissionTopology;不读本仓真实 workflow。",
            ["tools/tests/StrataLint.Tests/Commands/LeanReport/LeanReportInputScriptTests.cs"] =
                "生产脚本 lean-report-input.sh 自己解析 ci.yml(缺 job boundaries 即 SystemExit),"
                + "夹具必须喂它;被测的是该脚本的 producer-paths 派生。",
            ["tools/tests/StrataLint.Tests/FrozenLedger/FrozenLedgerDeltaPredicateTests.cs"] =
                "FrozenLedgerDeltaPredicate 把 ci.yml 列为 direct ledger input;测试复述生产数据,"
                + "不读该文件内容。",
        };

    private static readonly Regex WorkflowReference = new(
        @"\.github/workflows|""\.github""\s*,\s*""workflows""",
        RegexOptions.Compiled | RegexOptions.CultureInvariant);

    [Fact]
    public void NoTestSourceReferencesAWorkflowFile()
    {
        var violations = Scan().Select(hit => $"{hit.Path}:{hit.Line}").ToArray();

        Assert.True(
            violations.Length == 0,
            "对 workflow 的测试已被永久禁止(CLAUDE.md 器律⑦′):workflow 文本形状测试\n"
            + "只证明它长什么样,证明不了它会不会执行,唯一有效验证是让它在真实事件上跑一次。\n"
            + "请删除以下引用,而不是为它加豁免:\n  "
            + string.Join("\n  ", violations));
    }

    /// <summary>
    /// 放行侧的钉子:证明扫描确实选中了测试树,且本文件确实被自豁免掉(而非因扫不到而漏过)。
    /// 缺了它,把 <see cref="TestTreePrefix"/> 写成任何不存在的前缀都会让上一条恒绿。
    /// </summary>
    [Fact]
    public void ScanSelectsTheTestTreeAndNotTheProhibitionItself()
    {
        var root = RepositoryLayout.FindRoot();
        var scanned = GitIndexRepositoryFiles
            .EnumerateDeclared(root, TestTreePrefix)
            .Where(static file => file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .ToArray();

        Assert.NotEmpty(scanned);
        Assert.Contains(scanned, file => file.RelativePath == SelfPath);
        Assert.Matches(WorkflowReference, File.ReadAllText(Path.Combine(root, SelfPath)));
        Assert.DoesNotContain(Scan(), hit => hit.Path == SelfPath);
    }

    /// <summary>
    /// 豁免不得腐烂:每项都必须仍然存在、且仍然确实含 workflow 引用。某项一旦不再需要豁免,
    /// 本测试即红,强制把它从集合里删掉——这就是 removal-only 的机器形。
    /// </summary>
    [Fact]
    public void EveryExemptionIsStillPresentAndStillNeedsIt()
    {
        var root = RepositoryLayout.FindRoot();
        var tracked = GitIndexRepositoryFiles
            .EnumerateDeclared(root, TestTreePrefix)
            .ToDictionary(static file => file.RelativePath, static file => file.FullPath);

        Assert.All(ProductionConsumerExemptions, entry =>
        {
            Assert.True(
                tracked.TryGetValue(entry.Key, out var fullPath),
                $"豁免指向不存在的文件,请删除该项:{entry.Key}");
            Assert.True(
                WorkflowReference.IsMatch(File.ReadAllText(fullPath!)),
                $"该文件已不再引用 workflow,豁免是僵尸,请删除该项:{entry.Key}");
            Assert.False(string.IsNullOrWhiteSpace(entry.Value), $"豁免必须写明理由:{entry.Key}");
        });
    }

    private static IReadOnlyList<(string Path, int Line)> Scan()
    {
        var root = RepositoryLayout.FindRoot();
        var hits = new List<(string, int)>();

        foreach (var file in GitIndexRepositoryFiles.EnumerateDeclared(root, TestTreePrefix))
        {
            if (!file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                || file.RelativePath == SelfPath
                || ProductionConsumerExemptions.ContainsKey(file.RelativePath))
            {
                continue;
            }

            var lines = File.ReadAllLines(file.FullPath);
            for (var index = 0; index < lines.Length; index++)
            {
                if (WorkflowReference.IsMatch(lines[index]))
                {
                    hits.Add((file.RelativePath, index + 1));
                }
            }
        }

        return hits;
    }
}
