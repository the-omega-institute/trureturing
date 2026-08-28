using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeTestMapDeriverTests
{
    [Fact]
    public void TemporaryFileSystemRootReadIsNotARepositoryInput()
    {
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource("tools/tests/SyntheticTests.cs", """
                public sealed class SyntheticTests
                {
                    [Fact]
                    public void ReadsSyntheticProjection()
                    {
                        var temporary = TemporaryFileSystem.Directory.CreateTempSubdirectory();
                        _ = TemporaryFileSystem.File.ReadAllBytes(
                            Path.Combine(temporary.FullName, "projection.json"));
                    }
                }
                """)],
            []);

        var method = Assert.Single(map.Methods);
        Assert.Equal("SyntheticTests.ReadsSyntheticProjection", method.Id);
        Assert.Empty(method.Paths);
        Assert.Empty(method.UnknownReasons);
    }

    [Fact]
    public void RepositoryAccessorRootReadRemainsARepositoryInput()
    {
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource("tools/tests/SyntheticTests.cs", """
                public sealed class SyntheticTests
                {
                    [Fact]
                    public void ReadsRepositoryInput()
                    {
                        _ = RepositoryAccessor.ReadAllText(
                            RepositoryRelativePath.Create("Golden/input.txt"));
                    }
                }
                """)],
            []);

        var method = Assert.Single(map.Methods);
        Assert.Equal(["Golden/input.txt"], method.Paths);
        Assert.Empty(method.UnknownReasons);
    }

    // 夹具必须是**合法 XML 文档**:`IsXunitProject` 走 `XDocument.Parse`,
    // 裸元素片段会抛 XmlException。第一版正是这样让四条测试在基线就红的。
    private static string Project(string body) =>
        "<Project Sdk=\"Microsoft.NET.Sdk\"><ItemGroup>"
        + "<PackageReference Include=\"xunit\" Version=\"2.9.2\" />"
        + body
        + "</ItemGroup></Project>";

    /// <summary>放行侧:接线齐备的 xUnit 项目不得被判缺失。</summary>
    [Fact]
    public void DeterminismBanPredicateAcceptsAFullyWiredVerdictProject()
    {
        var wired = Project(
            "<PackageReference Include=\"Microsoft.CodeAnalysis.BannedApiAnalyzers\" />"
            + "<AdditionalFiles Include=\"../../Architecture/BannedSymbols.Determinism.txt\" />");

        Assert.Empty(ScribeTestMapDeriver.FindVerdictProjectsMissingDeterminismBan(
            [("tools/tests/Wired/Wired.csproj", wired)]));
    }

    /// <summary>拒绝侧三形:缺 AdditionalFiles / 缺 analyzer / 以 NoWarn 抑制 RS0030。</summary>
    [Theory]
    [InlineData("<PackageReference Include=\"Microsoft.CodeAnalysis.BannedApiAnalyzers\" />")]
    [InlineData("<AdditionalFiles Include=\"../../Architecture/BannedSymbols.Determinism.txt\" />")]
    [InlineData("<PackageReference Include=\"Microsoft.CodeAnalysis.BannedApiAnalyzers\" />"
        + "<AdditionalFiles Include=\"../../Architecture/BannedSymbols.Determinism.txt\" />"
        + "<NoWarn>$(NoWarn);RS0030</NoWarn>")]
    public void DeterminismBanPredicateRejectsAnIncompletelyWiredVerdictProject(string wiring)
    {
        var project = Assert.Single(ScribeTestMapDeriver.FindVerdictProjectsMissingDeterminismBan(
            [("tools/tests/Partial/Partial.csproj", Project(wiring))]));

        Assert.Equal("tools/tests/Partial/Partial.csproj", project);
    }

    /// <summary>
    /// 作用面:非 xUnit 项目与 tools/tests 之外的项目都不在判据内。
    /// 若没有这一条,两个 compile-fail-proof 项目会被误判。
    /// </summary>
    [Fact]
    public void DeterminismBanPredicateIgnoresNonVerdictProjects()
    {
        Assert.Empty(ScribeTestMapDeriver.FindVerdictProjectsMissingDeterminismBan(
        [
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", "<Project />"),
            ("tools/StrataLint.Engine/StrataLint.Engine.csproj", Project(string.Empty)),
        ]));
    }
}
