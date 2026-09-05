using System.Xml.Linq;
using TestProjectTopologyPolicy = StrataLint.Engine.RepositoryRules;

namespace StrataLint.ArchitectureTests;

// 本文件是 TestProjectTopologyPolicyTests 的 partial 分片:主文件加入这九条后达 903 行,
// 越过 SL-003 的 800 行硬线(判词见 PR #5433 的 admission 日志)。按第 8 条「桶满则裂」拆分,
// 分片键即议题(test→test 债的定义域,#5419),不是行数切割。
public sealed partial class TestProjectTopologyPolicyTests
{
    // ── test→test 债的定义域(#5419) ─────────────────────────────────────────
    //
    // 立这九条之前先测过:把定义域拆分实施完之后,既有 25 条**全部通过**,
    // 而同一棵真实仓库的债务集由 0 变 4。⟹ 既有套件对「主语面是谁」这条轴零覆盖,
    // 下列每一条都不是锦上添花,而是这条轴上唯一的钉子。

    private static TestProjectTopologyProject CrossCuttingHarness(params string[] references) =>
        ProjectWithDefaultProperties(CanonicalHarnessPath, "StrataLint.ArchitectureTests", true, references);

    private static TestProjectTopologyProject ScriptHarness(params string[] references) =>
        ProjectWithDefaultProperties(
            "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj",
            "StrataLint.ScriptTests",
            true,
            references);

    private static TestProjectTopologySnapshot HarnessWorld(
        params TestProjectTopologyProject[] extra) => Snapshot(
        [
            Production("NewProduct", "NewProduct"),
            OwnedTest("NewProduct.Tests", "NewProduct.Tests", "../../NewProduct/NewProduct.csproj"),
            .. extra,
        ]);

    [Fact]
    public void CrossCuttingHarnessReferencingAnOwnedTestIsTestToTestDebt()
    {
        var world = HarnessWorld(CrossCuttingHarness("../NewProduct.Tests/NewProduct.Tests.csproj"));

        var debt = TestProjectTopologyPolicy.CalculateDebt(world);

        Assert.Equal(
            [Debt("owned-test-to-owned-test-reference", "StrataLint.ArchitectureTests", "NewProduct.Tests")],
            debt.ToArray());
    }

    [Fact]
    public void CrossCuttingHarnessReferencingAnotherCrossCuttingHarnessIsAlsoDebt()
    {
        // 宾语侧:只扩主语会漏掉这一形。当前仓内无人这么写,故这条守的是空转的缺口 ——
        // 但它与被扩的那一侧是同一个错误类,分开只会让下一个人重新发现它。
        var world = HarnessWorld(
            ScriptHarness(
                "../StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj"),
            CrossCuttingHarness());

        var debt = TestProjectTopologyPolicy.CalculateDebt(world);

        Assert.Equal(
            [Debt("owned-test-to-owned-test-reference", "StrataLint.ScriptTests", "StrataLint.ArchitectureTests")],
            debt.ToArray());
    }

    [Fact]
    public void CrossCuttingHarnessWithoutTestReferencesStillCarriesNoOwnershipDebt()
    {
        // 收窄只动 test→test 那一侧;横跨型 harness 对**拥有关系**的豁免必须原样保留。
        var debt = TestProjectTopologyPolicy.CalculateDebt(HarnessWorld(CrossCuttingHarness()));

        Assert.Empty(debt);
    }

    [Fact]
    public void InheritedCrossCuttingTestReferenceIsAcceptedWhenUnchanged()
    {
        var world = HarnessWorld(CrossCuttingHarness("../NewProduct.Tests/NewProduct.Tests.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(world, world);

        Assert.True(result.IsAccepted, result.Message);
        Assert.Single(result.BaseDebt);
        Assert.Equal(result.BaseDebt.ToArray(), result.CandidateDebt.ToArray());
    }

    [Fact]
    public void NewCrossCuttingHarnessTestReferenceIsRejected()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            HarnessWorld(CrossCuttingHarness()),
            HarnessWorld(CrossCuttingHarness("../NewProduct.Tests/NewProduct.Tests.csproj")));

        Assert.False(result.IsAccepted);
        Assert.Equal(
            [Debt("owned-test-to-owned-test-reference", "StrataLint.ArchitectureTests", "NewProduct.Tests")],
            result.IntroducedDebt.ToArray());
    }

    [Fact]
    public void RemovingACrossCuttingTestReferenceStrictlyContracts()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            HarnessWorld(CrossCuttingHarness("../NewProduct.Tests/NewProduct.Tests.csproj")),
            HarnessWorld(CrossCuttingHarness()));

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.CandidateDebt);
        Assert.Single(result.RemovedDebt);
    }

    [Fact]
    public void EqualSizedCrossCuttingDebtSwapIsRejectedBySetContainment()
    {
        // 计数比较会放行「删一条、加另一条」;集合包含不会。
        var second = OwnedTest("Other.Tests", "Other.Tests", "../../Other/Other.csproj");
        var production = Production("Other", "Other");
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(
                [.. HarnessWorld(CrossCuttingHarness("../NewProduct.Tests/NewProduct.Tests.csproj")).Projects,
                 production, second]),
            Snapshot(
                [.. HarnessWorld(CrossCuttingHarness("../Other.Tests/Other.Tests.csproj")).Projects,
                 production, second]));

        Assert.False(result.IsAccepted);
        Assert.Equal(
            [Debt("owned-test-to-owned-test-reference", "StrataLint.ArchitectureTests", "Other.Tests")],
            result.IntroducedDebt.ToArray());
    }

    [Fact]
    public void UnrelatedHarnessPropertyEditRequiresNoDebtPayment()
    {
        // 实测依据(近 7 天,origin/dev):五个债务顶点 csproj 共被改 28 次,
        // 而可还的 test→test 边总共 4 条 ⟹ 粗粒度触发下第五个这样的 PR 起合法候选集合为空。
        // 故 test→test 债的参与者不计入路径级触发。
        var harness = CrossCuttingHarness("../NewProduct.Tests/NewProduct.Tests.csproj");
        var edited = new TestProjectTopologyProject(
            harness.Path,
            harness.Content.Replace("<ItemGroup>", "<ItemGroup><!-- unrelated --></ItemGroup><ItemGroup>"));

        var result = TestProjectTopologyPolicy.Evaluate(
            HarnessWorld(harness),
            HarnessWorld(edited));

        Assert.True(result.IsAccepted, result.Message);
        Assert.False(result.RequiresStrictReduction);
        Assert.Equal(result.BaseDebt.ToArray(), result.CandidateDebt.ToArray());
    }

    [Fact]
    public void EmptyBaseDebtStillRejectsANewCrossCuttingTestReference()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            HarnessWorld(),
            HarnessWorld(CrossCuttingHarness("../NewProduct.Tests/NewProduct.Tests.csproj")));

        Assert.False(result.IsAccepted);
        Assert.Empty(result.BaseDebt);
        Assert.Single(result.IntroducedDebt);
    }
}
