using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

// `FrozenLedgerMathlibReanchorTests.cs` 在 dev 上已是 795/800 行(SL-003 硬线 800),
// 装不下新用例;按第 8 条「桶满则裂」另开一片,而不是把它挤爆。
public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void MathlibReanchorAcceptsByteIdenticalSourceWithAnonymousLocalInstance()
    {
        const string source =
            "local instance (p : Prop) : Decidable p := Classical.propDecidable p\n"
            + "theorem a : True := by trivial\n";

        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    source,
                    statementMaterial: "old elaborated True",
                    declarations: ["a", "instDecidable_d5"]),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    source,
                    statementMaterial: "new elaborated True",
                    declarations: ["a", "instDecidable_d5"]),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }

    [Fact]
    public void MathlibReanchorAcceptsIndentedLocalNamedConstant()
    {
        // `constant` 在 Lean 4 不是声明关键字 —— 4.31 与 4.33 实测
        // `constant foo : Nat := 1` 均报 `unexpected identifier; expected command`,
        // 而 `def bar (constant : Nat) := constant - 0` 被接受。故一个缩进行以
        // `constant` 开头、行内又有 `:`(来自 `:=`)时,它是项而非缩进声明。
        // 本仓 D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.lean:489
        // 就是这个形状,曾使整条 mathlib 升级授权路径恒 false。
        const string source =
            "theorem a (constant : Nat) (step0 : Nat) : True := by\n"
            + "  have step :\n"
            + "      constant - (step0 : Nat) = constant - step0 := by\n"
            + "    rfl\n"
            + "  trivial\n";

        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport("A", source, statementMaterial: "old elaborated True"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport("A", source, statementMaterial: "new elaborated True"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade);

        Assert.NotNull(result.Recognition);
        Assert.True(result.Authorized);
        Assert.Null(result.Failure);
    }
}
