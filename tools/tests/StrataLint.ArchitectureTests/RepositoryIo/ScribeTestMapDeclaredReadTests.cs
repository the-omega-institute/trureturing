namespace StrataLint.ArchitectureTests;

/// <summary>
/// #3923 的认可形:「枚举一个已声明前缀,然后读该枚举结果的文件」。
///
/// **为什么单独一个文件**:这三条与 <c>ScribeTestMapDeriverTests</c> 同族,
/// 但那个文件在 dev 上已 767 行,加进去会到 830 —— **越过 SL-003 的 800 行硬线**
/// (`CapacityPolicyTests.RepositoryHasNoOversizeArtifactOrOverfullDirectory` 会红,
///  本次实测:257 通过 / 1 失败)。目录当前 10 个文件,加这一个到 11,仍在 12 的限内。
///
/// **三条的分工**(缺任一条,新认可形都会把 fail-closed 放掉):
/// ① 正例 —— 前缀是字面量、读的是该枚举结果 ⟹ known,且前缀进 Paths;
/// ② 跨前缀 —— 枚举 D5 却读 Blueprint ⟹ **不得**放行(该边界原 issue 未写,是补的);
/// ③ 无绑定 —— 与任何 EnumerateDeclared 无关的成员读 ⟹ 仍 VariablePath。
///
/// 「前缀本身是变量」那一侧由 <c>EnumerateDeclaredVariablePrefixIsUnknown</c> 守,
/// 在原文件里,**不要与本文件的三条混为一谈**。
/// </summary>
public sealed class ScribeTestMapDeclaredReadTests
{
    [Fact]
    public void EnumerateDeclaredLiteralPrefixReadFromEntryFullPathIsKnown()
    {
        const string source = """
            class DeclaredReadTests {
              [Fact] public void ReadsDeclaredFiles() {
                var contents = GitIndexRepositoryFiles
                  .EnumerateDeclared(RepositoryLayout.FindRoot(), "D5")
                  .Select(static entry => File.ReadAllText(entry.FullPath))
                  .ToArray();
              }
            }
            """;

        var method = Assert.Single(ScribeTestMapDeriverTests.DeriveSources([new("DeclaredReadTests.cs", source)]).Methods);

        Assert.Equal(["D5"], method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void EnumerateDeclaredD5DoesNotDeclareBlueprintMemberRead()
    {
        const string source = """
            class MismatchedDeclaredReadTests {
              [Fact] public void ReadsBlueprintInstead() {
                var blueprint = (
                  RelativePath: "Blueprint/Papers.scribe.cs",
                  FullPath: Path.Combine(
                    RepositoryLayout.FindRoot(),
                    "Blueprint",
                    "Papers.scribe.cs"));
                var contents = GitIndexRepositoryFiles
                  .EnumerateDeclared(RepositoryLayout.FindRoot(), "D5")
                  .Select(entry => File.ReadAllText(blueprint.FullPath))
                  .ToArray();
              }
            }
            """;

        var method = Assert.Single(ScribeTestMapDeriverTests.DeriveSources([new("MismatchedDeclaredReadTests.cs", source)]).Methods);

        Assert.Contains("D5", method.Paths);
        Assert.Equal(TestMapUnknownReason.VariablePath, Assert.Single(method.UnknownReasons));
    }

    [Fact]
    public void MemberFullPathReadWithoutEnumerateDeclaredIsUnknown()
    {
        const string source = """
            class UndeclaredMemberReadTests {
              [Fact] public void ReadsVariable() {
                var entry = Pick();
                File.ReadAllText(entry.FullPath);
              }
            }
            """;

        var method = Assert.Single(ScribeTestMapDeriverTests.DeriveSources([new("UndeclaredMemberReadTests.cs", source)]).Methods);

        Assert.Equal(TestMapUnknownReason.VariablePath, Assert.Single(method.UnknownReasons));
    }
}
