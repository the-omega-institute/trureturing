using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

// SyntheticNumberedAtomizer:被 15 个测试文件消费,原为 TheoryAtomizerTests.cs 末尾的一行。
// 它们此前住在一个以某测试类命名的文件里,消费面却比那个测试类大 ——
// 按文件名找不到。纯搬迁:类型、可见性、成员逐字不变;本文件不含测试方法。

internal static class SyntheticNumberedAtomizer { internal static string Id => AtomizerRegistry.GictId; }
