namespace StrataLint.Engine;

internal static class ObserverAtomizer
{
    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes)
    {
        var document = MarkdownAstAtomizer.Atomize(
            bytes, Identify, identifyFirstTableCellSource: Identify);
        if (document.Claims.Any(atom =>
                atom.AstPath.Contains("/occurrence/", StringComparison.Ordinal)))
        {
            throw new TheorySourceFormatException("duplicate observer claim locator");
        }

        return document;
    }

    private static string? Identify(string paragraph)
    {
        var locator = paragraph switch
        {
            _ when Starts(paragraph, "本文主张的是:") => "scope/kinematics-statistics",
            _ when Starts(paragraph, "**簿记条款(v2)**") => "scope/bookkeeping",
            _ when Starts(paragraph, "因果方向是本文的第一主张:") => "scope/forced-causal-direction",
            _ when Starts(paragraph, "因果方向:") => "scope/forced-causal-direction",
            _ when Starts(paragraph, "**(i) 相位对象。**") => "premise/phase-object",
            _ when Starts(paragraph, "**(ii) 刚性定律。**") => "premise/rigidity",
            _ when Starts(paragraph, "**(iii) 账本纪律。**") => "premise/ledger-discipline",
            _ when Starts(paragraph, "**语义地基(v2 一层重写)**") => "premise/semantic-foundation",
            _ when Starts(paragraph, "**定理(观察者代数的唯一形态)。**") => "theorem/observer-algebra",
            _ when Starts(paragraph, "**定理(观察者代数的典范形态)。**") => "theorem/observer-algebra",
            _ when Starts(paragraph, "**定理(有限窗口 = 素数量子寄存器)。**") => "theorem/finite-window-register",
            _ when Starts(paragraph, "**定理(有限窗口 = 素数量子寄存器,绕行限定版)。**") => "theorem/finite-window-register",
            _ when Starts(paragraph, "**定理(无经典答案表)。**") => "theorem/no-classical-answer-table",
            _ when Starts(paragraph, "**定理(无经典答案表,收窄版)。**") => "theorem/no-classical-answer-table",
            _ when Starts(paragraph, "**定理(叠加不违反经典刚性)。**") => "theorem/state-not-path",
            _ when Starts(paragraph, "**定理(观察者度量与二型无穷远,v2 新增)。**") => "theorem/observer-metric",
            _ when Starts(paragraph, "**定理(两族窗口二分法与黄金支,v3 新增)。**") => "theorem/window-dichotomy",
            _ when Starts(paragraph, "**测量的完整理论只有两个动词。**") => "measurement/conditioning",
            _ when Starts(paragraph, "**遗忘是可审计的数学关系。**") => "measurement/forgetting",
            _ when Starts(paragraph, "**时间的连续性是统计的产物。**") => "measurement/statistical-time",
            _ when Starts(paragraph, "**时间的连续性是统计的产物(热时间假设,诠释级)。**") => "measurement/statistical-time",
            _ when Starts(paragraph, "**中心层(强制,无选择)。**") => "classical/center",
            _ when Starts(paragraph, "**指针基层(由记账规则选定)。**") => "classical/pointer-basis",
            _ when Starts(paragraph, "**冗余层(集体记忆)。**") => "classical/redundant-records",
            _ when Starts(paragraph, "且单配定理锁死了") => "classical/unique-record",
            _ when Starts(paragraph, "单配定理锁死") => "classical/unique-record",
            _ when Starts(paragraph, "**v4 补全:经典性的账本签名与两种命运。**") => "classical/ledger-signature",
            _ when Starts(paragraph, "**Q1(为何有概率):推出。**") => "probability/Q1",
            _ when Starts(paragraph, "**Q2(为何恰是 $|\\psi|^2$):条件推出。**") => "probability/Q2",
            _ when Starts(paragraph, "**Q2(为何恰是 $|\\psi|^2$):条件推出(路线 B)。**") => "probability/Q2",
            _ when Starts(paragraph, "**Q3(为何单一结果):动力学谜化解,索引谜搬家。**") => "probability/Q3",
            _ when Starts(paragraph, "**Q4(概率何义)。**") => "probability/Q4",
            _ when Starts(paragraph, "**设置格(选问题)与记账格(选经典):判真。**") => "freedom/settings-and-recording",
            _ when Starts(paragraph, "**结果格(选答案):三重封死。**") => "freedom/outcome",
            _ when Starts(paragraph, "**整体格(全局单选):被隔离而非被否证。**") => "freedom/global",
            _ when Starts(paragraph, "**距离-相位定律。**") => "freedom/distance-phase",
            _ when Starts(paragraph, "**距离-相位定律三代(v2 全谱)。**") => "freedom/distance-phase",
            _ when Starts(paragraph, "**自由价目全表**") => "freedom/price-list",
            _ when Starts(paragraph, "**互补预算定理(v2 新增,自含四行证)。**") => "freedom/complementarity-budget",
            _ when Starts(paragraph, "Wigner 之友、") => "observer/nested-facts",
            _ when Starts(paragraph, "附带一行:PBR 定理") => "observer/pbr",
            _ when Starts(paragraph, "\"连续本不存在,连续是统计\"") => "physics/continuum-and-fields",
            _ when Starts(paragraph, "未具备者如实列出:") => "physics/open-geometry",
            _ when Starts(paragraph, "**已结案(八件,皆附证书):**") => "verdict/settled",
            _ when Starts(paragraph, "**已结案(附证书):**") => "verdict/settled",
            _ when Starts(paragraph, "**遗留(三类,性质各异):**") => "verdict/open",
            _ when Starts(paragraph, "**遗留(三类):**") => "verdict/open",
            _ when Starts(paragraph, "**总判词:**") => "verdict/final",
            _ when Starts(paragraph, "**§10.1 分层公共记忆中和原则**") => "memory/public-neutralization",
            _ when Starts(paragraph, "**§10.2 对数钟与通道谱(指针)**") => "memory/log-clock-channel-spectrum",
            _ when Starts(paragraph, "**§10.3 商余本体语义庭**") => "ontology/quotient-remainder",
            _ when Starts(paragraph, "**边界**") => "ontology/boundary",
            _ when Starts(paragraph, "**§11.1 章程(三定义,ZFC 内,零新公理)**") => "periodic-table/charter",
            _ when Starts(paragraph, "**§11.2 四问模板(逐层机械生成)**") => "periodic-table/four-question-template",
            _ when Starts(paragraph, "**§11.3 三科目终表(公理之辩四连案终审)**") => "periodic-table/axiom-hypothesis-definition",
            _ when Starts(paragraph, "**§11.4 首件产品指针**") => "periodic-table/first-product",
            _ when Starts(paragraph, "**§12.1 互反-干涉庭(\"真理一半看不见\")**") => "semantic-court/reciprocity-interference",
            _ when Starts(paragraph, "**§12.2 投影-干涉庭与署名**") => "semantic-court/projection-interference",
            _ when Starts(paragraph, "**§12.3 滤镜与视界庭(Fable/Mythos)**") => "semantic-court/filters-and-horizons",
            _ when Starts(paragraph, "**§13.1 商定理与首枚外部定理样本**") => "quotient-court/quotient-theorem",
            _ when Starts(paragraph, "**§13.2 对数钟之算术分店(指针)**") => "quotient-court/log-clock-arithmetic",
            _ when Starts(paragraph, "**§13.3 边界与署名**") => "quotient-court/boundary-signature",
            _ when Starts(paragraph, "**§14.1 定理脊柱(全部自含证明与证书,居本文辖区)**") => "formal-volume/theorem-spine",
            _ when Starts(paragraph, "**§14.2 合成判词与两条新焊缝**") => "formal-volume/synthesis-welds",
            _ when Starts(paragraph, "**§14.3 边界与申报**") => "formal-volume/boundary-declaration",
            _ when Starts(paragraph, "**§15.1 账本公理之定理化**") => "ledger-axioms/theoremization",
            _ when Starts(paragraph, "**§15.2 本体对象之谓词分家与投影族**") => "ledger-axioms/ontic-predicate-split",
            _ when Starts(paragraph, "**§15.3 边界与申报**") => "ledger-axioms/boundary-declaration",
            _ when Starts(paragraph, "**§16.1 观察者之钟(运动学定理三条 + 证书)**") => "observer-clock/clock-rate-theorems",
            _ when Starts(paragraph, "**§16.2 形与签(本文主张之二分定理化)**") => "observer-clock/form-signature-split",
            _ when Starts(paragraph, "**§16.3 测量论之算术同址(指针)**") => "observer-clock/measurement-arithmetic",
            _ when Starts(paragraph, "**§17.1 六环链(本文测量论之链式定理化)**") => "chain-court/six-link-chain",
            _ when Starts(paragraph, "**§17.2 双柱贯链(熵-自由对偶升为簿记法)**") => "chain-court/double-column-ledger",
            _ when Starts(paragraph, "**§17.3 测量几何与算术同址续报(指针)**") => "chain-court/measurement-geometry-pointer",
            _ when Starts(paragraph, "**§18.1 文体定名**") => "ledger-machine/genre-naming",
            _ when Starts(paragraph, "**§18.2 机器全貌(编号引用,零新假设)**") => "ledger-machine/full-picture",
            _ when Starts(paragraph, "**§18.3 三词收官与边界**") => "ledger-machine/three-word-closure",
            _ when Starts(paragraph, "**§19.1 非是集(以否定完成定位)**") => "machine-negations/negative-set",
            _ when Starts(paragraph, "**§19.2 教学面(入门件指针)**") => "machine-negations/teaching-surface",
            _ when Starts(paragraph, "**§19.3 能量与力(运动学词条 + 墙)**") => "machine-negations/energy-and-force",
            _ when Starts(paragraph, "**§20.1 熵之相对论(本文核心命题之收官形)**") => "entropy-relativity/relativity-of-entropy",
            _ when Starts(paragraph, "**§20.2 动力学合流与 Wick 指针(界限申报)**") => "entropy-relativity/wick-pointer",
            _ when Starts(paragraph, "**§20.3 谱之双重身份与子系统概念之三重松动**") => "entropy-relativity/spectrum-dual-identity",
            _ when Starts(paragraph, "**§21.1 总装卷之本文定位**") => "assembly-volume/positioning",
            _ when Starts(paragraph, "**§21.2 观察者代价定理(本批新增之 OQ 切片)**") => "assembly-volume/observer-cost-theorem",
            _ when Starts(paragraph, "**§21.3 结构出身与收官**") => "assembly-volume/structural-origin",
            _ => null,
        };
        if (locator is null && HasBoldClaimLead(paragraph))
        {
            throw new TheorySourceFormatException(
                $"unknown observer claim lead '{TheorySourceFormatException.ClaimLead(paragraph)}'");
        }

        return locator;
    }

    private static bool Starts(string paragraph, string prefix) =>
        paragraph.StartsWith(prefix, StringComparison.Ordinal);

    private static bool HasBoldClaimLead(string paragraph)
    {
        var index = 0;
        while (index < paragraph.Length && paragraph[index] is ' ' or '\t')
        {
            index++;
        }

        return paragraph.AsSpan(index).StartsWith("**", StringComparison.Ordinal);
    }
}
