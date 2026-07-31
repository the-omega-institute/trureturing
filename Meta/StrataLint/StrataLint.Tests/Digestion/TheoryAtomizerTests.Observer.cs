using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    [Fact]
    public void ObserverAdapterRecognizesEveryProductionClaim()
    {
        var root = FindRepositoryRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, ThirdProductionSource));

        var document = AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes);

        AssertRecognitionComplete(document, bytes);
    }

    [Fact]
    public void ObserverV1RecognizesTheObserverQuantumRefreshDialect()
    {
        var bytes = Encoding.UTF8.GetBytes(
            """
            # Observer refresh

            本文主张的是:claim。

            **簿记条款(v2)**:claim。

            因果方向:claim。

            **(i) 相位对象。** claim。

            **(ii) 刚性定律。** claim。

            **(iii) 账本纪律。** claim。

            **语义地基(v2 一层重写)**:claim。

            **定理(观察者代数的典范形态)。** claim。

            **定理(有限窗口 = 素数量子寄存器,绕行限定版)。** claim。

            **定理(无经典答案表,收窄版)。** claim。

            **定理(叠加不违反经典刚性)。** claim。

            **定理(观察者度量与二型无穷远,v2 新增)。** claim。

            **定理(两族窗口二分法与黄金支,v3 新增)。** claim。

            **测量的完整理论只有两个动词。** claim。

            **遗忘是可审计的数学关系。** claim。

            **时间的连续性是统计的产物(热时间假设,诠释级)。** claim。

            **中心层(强制,无选择)。** claim。

            **指针基层(由记账规则选定)。** claim。

            **冗余层(集体记忆)。** claim。

            单配定理锁死 claim。

            **v4 补全:经典性的账本签名与两种命运。** claim。

            **Q1(为何有概率):推出。** claim。

            **Q2(为何恰是 $|\psi|^2$):条件推出(路线 B)。** claim。

            **Q3(为何单一结果):动力学谜化解,索引谜搬家。** claim。

            **Q4(概率何义)。** claim。

            **设置格(选问题)与记账格(选经典):判真。** claim。

            **距离-相位定律三代(v2 全谱)。** claim。

            **自由价目全表**:claim。

            **互补预算定理(v2 新增,自含四行证)。** claim。

            Wigner 之友、claim。

            "连续本不存在,连续是统计" claim。

            未具备者如实列出:claim。

            **已结案(附证书):** claim。

            **遗留(三类):** claim。

            **总判词:** claim。

            **§10.1 分层公共记忆中和原则**。claim。

            **§10.2 对数钟与通道谱(指针)**。claim。

            **§10.3 商余本体语义庭**。claim。

            **边界**。claim。
            """);

        var document = AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes);

        Assert.Equal(
            [
                "scope/kinematics-statistics",
                "scope/bookkeeping",
                "scope/forced-causal-direction",
                "premise/phase-object",
                "premise/rigidity",
                "premise/ledger-discipline",
                "premise/semantic-foundation",
                "theorem/observer-algebra",
                "theorem/finite-window-register",
                "theorem/no-classical-answer-table",
                "theorem/state-not-path",
                "theorem/observer-metric",
                "theorem/window-dichotomy",
                "measurement/conditioning",
                "measurement/forgetting",
                "measurement/statistical-time",
                "classical/center",
                "classical/pointer-basis",
                "classical/redundant-records",
                "classical/unique-record",
                "classical/ledger-signature",
                "probability/Q1",
                "probability/Q2",
                "probability/Q3",
                "probability/Q4",
                "freedom/settings-and-recording",
                "freedom/distance-phase",
                "freedom/price-list",
                "freedom/complementarity-budget",
                "observer/nested-facts",
                "physics/continuum-and-fields",
                "physics/open-geometry",
                "verdict/settled",
                "verdict/open",
                "verdict/final",
                "memory/public-neutralization",
                "memory/log-clock-channel-spectrum",
                "ontology/quotient-remainder",
                "ontology/boundary",
            ],
            document.Claims.Select(static item => item.AstPath));
        AssertRecognitionComplete(document, bytes);
    }

    [Theory]
    [InlineData("**§13.1 商定理与首枚外部定理样本**。claim。", "quotient-court/quotient-theorem")]
    [InlineData("**§13.2 对数钟之算术分店(指针)**。claim。", "quotient-court/log-clock-arithmetic")]
    [InlineData("**§13.3 边界与署名**。claim。", "quotient-court/boundary-signature")]
    [InlineData("**§14.1 定理脊柱(全部自含证明与证书,居本文辖区)**。claim。", "formal-volume/theorem-spine")]
    [InlineData("**§14.2 合成判词与两条新焊缝**。claim。", "formal-volume/synthesis-welds")]
    [InlineData("**§14.3 边界与申报**。claim。", "formal-volume/boundary-declaration")]
    [InlineData("**§15.1 账本公理之定理化**。claim。", "ledger-axioms/theoremization")]
    [InlineData("**§15.2 本体对象之谓词分家与投影族**。claim。", "ledger-axioms/ontic-predicate-split")]
    [InlineData("**§15.3 边界与申报**。claim。", "ledger-axioms/boundary-declaration")]
    [InlineData("**§16.1 观察者之钟(运动学定理三条 + 证书)**。claim。", "observer-clock/clock-rate-theorems")]
    [InlineData("**§16.2 形与签(本文主张之二分定理化)**。claim。", "observer-clock/form-signature-split")]
    [InlineData("**§16.3 测量论之算术同址(指针)**。claim。", "observer-clock/measurement-arithmetic")]
    public void ObserverV1RecognizesTheV61ThroughV64CourtClaimLeads(
        string claim,
        string expectedAstPath)
    {
        var bytes = Encoding.UTF8.GetBytes($"# Observer\n\n{claim}\n");

        var atom = Assert.Single(AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes).Claims);

        Assert.Equal(expectedAstPath, atom.AstPath);
    }

    [Theory]
    [InlineData("**§17.1 六环链(本文测量论之链式定理化)**。claim。", "chain-court/six-link-chain")]
    [InlineData("**§17.2 双柱贯链(熵-自由对偶升为簿记法)**。claim。", "chain-court/double-column-ledger")]
    [InlineData("**§17.3 测量几何与算术同址续报(指针)**。claim。", "chain-court/measurement-geometry-pointer")]
    [InlineData("**§18.1 文体定名**。claim。", "ledger-machine/genre-naming")]
    [InlineData("**§18.2 机器全貌(编号引用,零新假设)**。claim。", "ledger-machine/full-picture")]
    [InlineData("**§18.3 三词收官与边界**。claim。", "ledger-machine/three-word-closure")]
    [InlineData("**§19.1 非是集(以否定完成定位)**。claim。", "machine-negations/negative-set")]
    [InlineData("**§19.2 教学面(入门件指针)**。claim。", "machine-negations/teaching-surface")]
    [InlineData("**§19.3 能量与力(运动学词条 + 墙)**。claim。", "machine-negations/energy-and-force")]
    [InlineData("**§20.1 熵之相对论(本文核心命题之收官形)**。claim。", "entropy-relativity/relativity-of-entropy")]
    [InlineData("**§20.2 动力学合流与 Wick 指针(界限申报)**。claim。", "entropy-relativity/wick-pointer")]
    [InlineData("**§20.3 谱之双重身份与子系统概念之三重松动**。claim。", "entropy-relativity/spectrum-dual-identity")]
    [InlineData("**§21.1 总装卷之本文定位**。claim。", "assembly-volume/positioning")]
    [InlineData("**§21.2 观察者代价定理(本批新增之 OQ 切片)**。claim。", "assembly-volume/observer-cost-theorem")]
    [InlineData("**§21.3 结构出身与收官**。claim。", "assembly-volume/structural-origin")]
    public void ObserverV1RecognizesTheV65ThroughV69CourtClaimLeads(
        string claim,
        string expectedAstPath)
    {
        var bytes = Encoding.UTF8.GetBytes($"# Observer\n\n{claim}\n");

        var atom = Assert.Single(AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes).Claims);

        Assert.Equal(expectedAstPath, atom.AstPath);
    }
}
