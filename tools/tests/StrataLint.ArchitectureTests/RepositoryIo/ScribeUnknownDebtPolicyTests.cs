using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

/// <summary>
/// `ScribeUnknownDebtPolicy` 此前**没有任何直接测试**(全仓唯一调用点是
/// `RepositoryRules.Structure.cs`)。本文件既是搬迁语义的判据,也补上那笔测试债。
///
/// 被治理的命题:unknown 身份是 `(PartitionKey, SourcePath, Id)`,**位置在身份里**,
/// 于是把一个 unknown 测试方法从一个项目/文件搬到另一处,会被判为 `introduced` 而拒 ——
/// 尽管搬迁**既不增也不减** parser 债。见 #5419。
/// </summary>
public sealed class ScribeUnknownDebtPolicyTests
{
    [Fact]
    public void RelocatedUnknownMethodIsNotIntroduced()
    {
        var result = Evaluate(
            Map(Unknown("A", "a/One.cs", "Suite.Probe")),
            Map(Unknown("B", "b/One.cs", "Suite.Probe")));

        Assert.Empty(Blocks(result));
    }

    [Fact]
    public void GenuinelyNewUnknownMethodIsStillIntroduced()
    {
        var result = Evaluate(
            Map(Unknown("A", "a/One.cs", "Suite.Probe")),
            Map(
                Unknown("A", "a/One.cs", "Suite.Probe"),
                Unknown("A", "a/Two.cs", "Suite.Other")));

        Assert.Equal(["a/Two.cs"], Blocks(result).Select(static f => f.Path).ToArray());
    }

    [Fact]
    public void RelocationDoesNotExcuseAnUnrelatedNewUnknown()
    {
        var result = Evaluate(
            Map(Unknown("A", "a/One.cs", "Suite.Probe")),
            Map(
                Unknown("B", "b/One.cs", "Suite.Probe"),
                Unknown("B", "b/Two.cs", "Suite.Fresh")));

        Assert.Equal(["b/Two.cs"], Blocks(result).Select(static f => f.Path).ToArray());
    }

    [Fact]
    public void RelocationRequiresTheOriginalToBeGone()
    {
        // 原处仍在 ⟹ 没有搬迁,只是复制 ⟹ 债实增一条。
        var result = Evaluate(
            Map(Unknown("A", "a/One.cs", "Suite.Probe")),
            Map(
                Unknown("A", "a/One.cs", "Suite.Probe"),
                Unknown("B", "b/One.cs", "Suite.Probe")));

        Assert.Equal(["b/One.cs"], Blocks(result).Select(static f => f.Path).ToArray());
    }

    [Fact]
    public void RelocationRequiresTheSameUnknownReasons()
    {
        // 同名但成因不同 ⟹ 不是同一笔债,不得互抵。
        var result = Evaluate(
            Map(Unknown("A", "a/One.cs", "Suite.Probe", TestMapUnknownReason.Other)),
            Map(Unknown("B", "b/One.cs", "Suite.Probe", TestMapUnknownReason.VariablePath)));

        Assert.Equal(["b/One.cs"], Blocks(result).Select(static f => f.Path).ToArray());
    }

    [Fact]
    public void OneRemovalExcusesOnlyOneRelocation()
    {
        // 抵扣是**配对**不是谓词:删一条不能豁免两条同名新增。
        var result = Evaluate(
            Map(Unknown("A", "a/One.cs", "Suite.Probe")),
            Map(
                Unknown("B", "b/One.cs", "Suite.Probe"),
                Unknown("C", "c/One.cs", "Suite.Probe")));

        Assert.Single(Blocks(result));
    }

    [Fact]
    public void TwoRemovalsExcuseTwoRelocations()
    {
        var result = Evaluate(
            Map(
                Unknown("A", "a/One.cs", "Suite.Probe"),
                Unknown("A", "a/Two.cs", "Suite.Other")),
            Map(
                Unknown("B", "b/One.cs", "Suite.Probe"),
                Unknown("B", "b/Two.cs", "Suite.Other")));

        Assert.Empty(Blocks(result));
    }

    private static ScribeUnknownDebtFinding[] Blocks(
        IEnumerable<ScribeUnknownDebtFinding> findings) => findings
        .Where(static finding => finding.Effect == AdmissionEffect.Block)
        .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
        .ToArray();

    private static IEnumerable<ScribeUnknownDebtFinding> Evaluate(
        ScribeTestMap forkPoint,
        ScribeTestMap current) => ScribeUnknownDebtPolicy.Evaluate(current, forkPoint);

    private static ScribeTestMap Map(params ScribeTestMethod[] methods) =>
        new(methods, [], [], [], []);

    private static ScribeTestMethod Unknown(
        string partition,
        string path,
        string id,
        TestMapUnknownReason reason = TestMapUnknownReason.Other) =>
        new(partition, path, id, [reason]);
}
