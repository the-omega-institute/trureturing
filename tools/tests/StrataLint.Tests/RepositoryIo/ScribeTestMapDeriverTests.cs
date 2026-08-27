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

    [Fact]
    public void BoundedEnumerationIsUnknownWhenReadPrecedesFilter()
    {
        AssertBoundedEnumerationIsUnknown("""
            GitIndexRepositoryFiles.Enumerate(RepositoryLayout.FindRoot())
                .Select(file =>
                {
                    _ = XDocument.Load(file.FullPath, LoadOptions.None);
                    return file;
                })
                .Where(file => file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal))
                .ToArray()
            """);
    }

    [Fact]
    public void BoundedEnumerationIsUnknownWhenPrefixUsesNestedLambdaBinding()
    {
        AssertBoundedEnumerationIsUnknown("""
            GitIndexRepositoryFiles.Enumerate(RepositoryLayout.FindRoot())
                .Where(file => new[] { file }.Any(candidate =>
                    candidate.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)))
                .Select(file => XDocument.Load(file.FullPath, LoadOptions.None))
                .ToArray()
            """);
    }

    [Fact]
    public void BoundedEnumerationIsUnknownForUnmodeledContentReadApi()
    {
        AssertBoundedEnumerationIsUnknown("""
            GitIndexRepositoryFiles.Enumerate(RepositoryLayout.FindRoot())
                .Where(file => file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal))
                .Select(file => File.OpenRead(file.FullPath))
                .ToArray()
            """);
    }

    [Fact]
    public void BoundedEnumerationIsUnknownOutsideTrackedTestScope()
    {
        AssertBoundedEnumerationIsUnknown("""
            GitIndexRepositoryFiles.Enumerate(RepositoryLayout.FindRoot())
                .Where(file => file.RelativePath.StartsWith("tools/scripts/", StringComparison.Ordinal))
                .Select(file => XDocument.Load(file.FullPath, LoadOptions.None))
                .ToArray()
            """);
    }

    [Fact]
    public void BoundedEnumerationIsUnknownWithInsertedOperator()
    {
        AssertBoundedEnumerationIsUnknown("""
            GitIndexRepositoryFiles.Enumerate(RepositoryLayout.FindRoot())
                .Where(file => file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal))
                .OrderBy(file => file.RelativePath)
                .Select(file => XDocument.Load(file.FullPath, LoadOptions.None))
                .ToArray()
            """);
    }

    [Fact]
    public void BoundedEnumerationIsUnknownWhenPrefixIsDisjunctive()
    {
        AssertBoundedEnumerationIsUnknown("""
            GitIndexRepositoryFiles.Enumerate(RepositoryLayout.FindRoot())
                .Where(file => file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
                    || true)
                .Select(file => XDocument.Load(file.FullPath, LoadOptions.None))
                .ToArray()
            """);
    }

    private static void AssertBoundedEnumerationIsUnknown(string expression)
    {
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource("tools/tests/SyntheticTests.cs", $$"""
                public sealed class SyntheticTests
                {
                    [Fact]
                    public void ReadsTrackedTests()
                    {
                        _ = {{expression}};
                    }
                }
                """)],
            []);

        var method = Assert.Single(map.Methods);
        Assert.True(method.IsUnknown);
        Assert.Equal(TestMapUnknownReason.Other, Assert.Single(method.UnknownReasons));
    }
}
