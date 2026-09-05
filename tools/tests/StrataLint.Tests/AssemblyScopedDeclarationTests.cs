namespace StrataLint.Tests;

/// <summary>
/// 程序集级声明(<c>global using</c> 别名、<c>[assembly:]</c> 属性)对**整个程序集**生效,
/// 却由**某一个文件**承载;文件一旦被迁走,声明跟着走而原程序集静默失效 —— 编译仍绿。
/// 本 PR 把它们从 TestProcessRunner.cs / TestScratchRoot.cs 收进 Usings.cs 与
/// AssemblyInfo.cs,本类是那次收拢的机器判据。
/// </summary>
public sealed class AssemblyScopedDeclarationTests
{
    /// <summary>
    /// 别名丢失不会让任何东西编译失败 —— <c>[Fact]</c> 只是静默退回 xUnit 原生实现,
    /// 于是全程序集的 Skippable 语义一起消失而无人察觉。此断言把该别名钉成**编译期**身份:
    /// 别名被删或改指,此处即红。
    /// </summary>
    [Fact]
    public void FactAndTheoryResolveToTheSkippableImplementations()
    {
        Assert.Equal(typeof(Xunit.SkippableFactAttribute), typeof(FactAttribute));
        Assert.Equal(typeof(Xunit.SkippableTheoryAttribute), typeof(TheoryAttribute));
    }

    /// <summary>
    /// <c>[assembly: TestFramework(...)]</c> 的第二个实参是承载它的**那个程序集**的名字。
    /// 该属性若随某个被迁走的类型离开本程序集,测试发现会整体改道而编译不红;
    /// 此断言从本程序集自身读回该属性,故属性一旦不在本程序集即红。
    /// 用 <c>CustomAttributeData</c> 而非强类型读取:实参值才是承重的东西,
    /// 而该属性类型在本 xunit 版本下不对测试项目公开可解析。
    /// </summary>
    [Fact]
    public void TestFrameworkRegistrationStaysInThisAssembly()
    {
        var registration = typeof(AssemblyScopedDeclarationTests).Assembly
            .GetCustomAttributesData()
            .Single(data => data.AttributeType.Name == "TestFrameworkAttribute");
        Assert.Equal(
            ["StrataLint.Tests.TestScratchFramework", "StrataLint.Tests"],
            registration.ConstructorArguments.Select(static argument => argument.Value).ToArray());
    }
}
