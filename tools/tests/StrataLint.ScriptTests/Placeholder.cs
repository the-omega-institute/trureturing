namespace StrataLint.Tests;

/// <summary>
/// 脚本测试程序集的落点。本层只立项目与其在拓扑策略里的分类,不搬任何测试类 ——
/// 搬迁牵动三条独立约束(partial class 闭包、RepositoryIoAccessPolicy 的豁免棘轮、
/// 跨测试程序集的 InternalsVisibleTo 链),每条都够单独一层。
///
/// 该断言证明程序集真被构建与执行,而不是一个从未运行的空壳。
/// </summary>
public sealed class ScriptTestAssemblyTests
{
    [Fact]
    public void AssemblyIsBuiltAndExecuted() =>
        Assert.Equal(
            "StrataLint.ScriptTests",
            typeof(ScriptTestAssemblyTests).Assembly.GetName().Name);
}
