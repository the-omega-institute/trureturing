using System.Runtime.CompilerServices;
using Xunit;

// 脚手架保持 internal 且单一归属于本程序集;脚本测试程序集经此具名可见性取用,
// 不复制源文件(共享编译项会被 SL-003 判 MSBuild Compile ownership ambiguous)。
[assembly: InternalsVisibleTo("StrataLint.ScriptTests")]

// ArchitectureTests 取用本程序集的 internal 脚手架做架构断言。
[assembly: InternalsVisibleTo("StrataLint.ArchitectureTests")]

// xUnit 测试框架注册。**属性本身**必须留在本程序集(它决定本程序集的测试如何被发现与执行),
// 故它不该住在任何可能被迁走的助手文件里 —— 它此前住在 TestScratchRoot.cs。
//
// 但**第二个实参不是「本程序集的名字」**。xUnit 的 API 文档原文:
//   assemblyName: The name of the assembly that the test framework **type is located in**,
//                 without file extension (f.e., 'xunit.execution')
// 即它指的是 **TestScratchFramework 这个类型所在的程序集**,只是当前二者恰好同为
// StrataLint.Tests,故两种读法在现状下无法区分。
//
// 这条勘正有实际后果:框架类型**可以**迁往别处(如 StrataLint.TestSupport),
// 只需同步更新此实参 —— 而我先前写的「不得随任何被引用的类型迁走」会让读者以为不行,
// 从而误判共享脚手架的可迁移面(见 #5419 的 L3)。
[assembly: TestFramework("StrataLint.TestSupport.TestScratchFramework", "StrataLint.TestSupport")]
