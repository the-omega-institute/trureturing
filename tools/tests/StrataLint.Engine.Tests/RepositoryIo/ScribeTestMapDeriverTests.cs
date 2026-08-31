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

    [Fact]
    public void CandidateSourceIdentitySetIncludesStaticallySkippedFacts()
    {
        const string source = "tools/tests/Synthetic.Tests/SkippedTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class SkippedTests
                {
                    [Fact(Skip = "candidate disabled a protected-base planned test")]
                    public void ProtectedBasePlanned() { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project });
        var method = Assert.Single(map.Methods);
        Assert.True(method.IsStaticallySkipped);
        Assert.Empty(method.RuntimeConditionalSkipReasons);
        Assert.Empty(method.RuntimeConditionalSkipContracts);

        var identities = EngineeringTestPlanPolicy.SourceIdentities(
            map,
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [project] = "Synthetic.Custom.Tests",
            });

        var identity = Assert.Single(identities);
        Assert.Equal("Synthetic.Custom.Tests", identity.Assembly);
        Assert.Equal("SkippedTests.ProtectedBasePlanned", identity.Id);
    }
}
