using System.Reflection;

namespace StrataLint.Scribe.Tests;

// 文档已迁出 StrataLint.Scribe —— 它们住 StrataLint.Scribe.Documents,而本测试程序集
// 刻意不引用那个工程:文档是数据,能编译即可,不为它建测试(owner 2026-09-05 裁决)。
// 下列 CLI 测试都在自建的临时仓库上跑,不需要真语料;引擎程序集里现在一个
// IScribeDocumentDefinition 都没有,故它就是「零文档」这个意思的唯一真源。
// 不可用本测试程序集代替 —— DocumentDiscoveryTests 里住着一个故意造坏的
// MismatchedDefinition,发现它会抛错。
internal static class DocumentlessAssembly
{
    internal static Assembly Value { get; } = typeof(ScribeCli).Assembly;
}
