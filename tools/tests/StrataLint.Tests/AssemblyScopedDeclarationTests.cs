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

    // 这里曾有第二颗钉子,用 `Assembly.GetCustomAttributesData()` 断言
    // `[assembly: TestFramework(...)]` 仍在本程序集。**已撤销,不是遗漏。**
    //
    // SL-003 判它 `conservative unknown test method introduced after fork point`
    // (判词见 PR #5420 的 admission 判官日志)。根因在
    // ScribeTestSymbolBinder:`IsReflectionDispatch(...) && CompileTimeInputUniverses.Count == 0`
    // ⟹ `TestMapUnknownReason.Other`。**该分类是对的** —— 反射的输入域在编译期无界,
    // 而「属性是否还在本程序集」这件事**只能靠反射观察**,故不存在既守得住又 known 的写法
    // (`[CompileTimeInputUniverse]` 是给仓库**路径**域用的,套在程序集属性上是误用)。
    //
    // 真正的修法是结构性的、且已在本 PR 落地:该属性从 TestScratchRoot.cs 迁进
    // AssemblyInfo.cs 之后,它不再住在任何会被迁走的助手文件里 —— 失效模式本身消失,
    // 不是被检测捕获。为一颗补充性的钉子去欠 unknown 债不划算。
    //
    // 残留风险如实记 `open`:若有人把该属性再搬出 AssemblyInfo.cs,当前无机器发现;
    // 症状是 TestScratchRoot 不再被收尾释放(临时目录泄漏),**静默**。
}
