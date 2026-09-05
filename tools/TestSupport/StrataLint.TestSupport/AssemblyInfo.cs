using System.Runtime.CompilerServices;

// TestProcessRunner 保持 internal:它的返回类型 ProcessOutput 是 Engine 的 internal,
// 公开成员无法暴露它。故由本程序集具名授权给三个消费方,而不是把类型改 public。
[assembly: InternalsVisibleTo("StrataLint.Tests")]
[assembly: InternalsVisibleTo("StrataLint.ScriptTests")]
[assembly: InternalsVisibleTo("StrataLint.ArchitectureTests")]
