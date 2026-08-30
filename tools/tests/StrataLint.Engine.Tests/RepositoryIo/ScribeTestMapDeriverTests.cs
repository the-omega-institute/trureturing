using StrataLint.Engine;

namespace StrataLint.Engine.Tests;

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
}
