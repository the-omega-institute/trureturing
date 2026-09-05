using System.Runtime.CompilerServices;
using Xunit;

// 脚手架保持 internal 且单一归属于本程序集;脚本测试程序集经此具名可见性取用,
// 不复制源文件(共享编译项会被 SL-003 判 MSBuild Compile ownership ambiguous)。
[assembly: InternalsVisibleTo("StrataLint.ScriptTests")]

// ArchitectureTests 取用本程序集的 internal 脚手架做架构断言。
[assembly: InternalsVisibleTo("StrataLint.ArchitectureTests")]

// xUnit 测试框架注册。第二个实参是**本程序集的名字**,故此声明必须留在本程序集,
// 且不得随任何被引用的类型迁走 —— 它此前住在 TestScratchRoot.cs 里,
// 搬那个文件就会把整个程序集的测试发现一并搬走。
[assembly: TestFramework("StrataLint.Tests.TestScratchFramework", "StrataLint.Tests")]
