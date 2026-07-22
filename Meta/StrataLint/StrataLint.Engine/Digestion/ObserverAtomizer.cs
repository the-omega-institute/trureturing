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
