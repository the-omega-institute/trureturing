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
    public void CompileTimeInputUniverseRecordsOnlyMatchingNewCompileInput()
    {
        const string testProject = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        const string testSource = "tools/tests/Synthetic.Tests/UniverseTests.cs";
        const string productionProject = "src/Corpus/Corpus.csproj";
        const string productionSource = "src/Corpus/Definitions.cs";
        var tracked = new ScribeTrackedSource[]
        {
            new(testProject, """
                <Project Sdk="Microsoft.NET.Sdk">
                  <ItemGroup>
                    <PackageReference Include="xunit" Version="2.9.3" />
                    <ProjectReference Include="../../../src/Corpus/Corpus.csproj" />
                  </ItemGroup>
                </Project>
                """),
            new(testSource, """
                using StrataLint.Engine;
                using Xunit;

                public sealed class UniverseTests
                {
                    [Fact]
                    public void ReadsCompiledDefinitions() => _ = Definitions.All;
                }
                """),
            new(productionProject, "<Project Sdk=\"Microsoft.NET.Sdk\" />"),
            new(productionSource, """
                NAMESPACE StrataLint.Engine
                {
                    [AttributeUsage(AttributeTargets.Property)]
                    public sealed class CompileTimeInputUniverseAttribute(
                        string prefix,
                        string suffix) : Attribute;

                    public static class Definitions
                    {
                        [CompileTimeInputUniverse("Blueprint/", ".scribe.cs")]
                        public static object All => new();
                    }
                }
                """.Replace("NAMESPACE", "name" + "space", StringComparison.Ordinal)),
        };
        var projectBySource = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [testSource] = testProject,
            [productionSource] = productionProject,
        };
        var context = ScribeProjectCompilationContext.Create(
            tracked,
            projectBySource,
            new HashSet<string>(StringComparer.Ordinal) { testProject });
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(testSource, tracked.Single(file => file.Path == testSource).Content)],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [testSource] = testProject },
            productionAssemblies: context.ProductionAssemblies,
            compilationContext: context);

        var method = Assert.Single(map.Methods);
        var universe = Assert.Single(method.CompileTimeInputUniverses);
        Assert.True(universe.Covers("Blueprint/D5/S3/NewDefinition.scribe.cs"));
        Assert.False(universe.Covers("Blueprint/D5/S3/NewDefinition.md"));
    }

    [Fact]
    public void CompileTimeInputUniverseFlowsThroughAnUnmarkedProductionPropertyWrapper()
    {
        var map = DeriveCompileTimeInputUniverseMap(
            "_ = DefinitionWrapper.All;",
            "public static object All => Definitions.All;");

        var method = Assert.Single(map.Methods);

        Assert.Empty(method.UnknownReasons);
        Assert.True(Assert.Single(method.CompileTimeInputUniverses)
            .Covers("Blueprint/D5/S3/NewDefinition.scribe.cs"));
    }

    [Fact]
    public void UnmarkedReflectionWrapperAroundCompileTimeUniverseFailsClosedWithASignal()
    {
        var map = DeriveCompileTimeInputUniverseMap(
            "_ = DefinitionWrapper.All;",
            """
            public static object? All => typeof(Definitions)
                .GetProperty("All")!
                .GetValue(null);
            """);

        var method = Assert.Single(map.Methods);

        Assert.Equal(TestMapUnknownReason.Other, Assert.Single(method.UnknownReasons));
        Assert.Empty(method.CompileTimeInputUniverses);
    }

    private static ScribeTestMap DeriveCompileTimeInputUniverseMap(
        string testStatement,
        string wrapperMember)
    {
        const string testProject = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        const string testSource = "tools/tests/Synthetic.Tests/UniverseTests.cs";
        const string productionProject = "src/Corpus/Corpus.csproj";
        const string productionSource = "src/Corpus/Definitions.cs";
        var tracked = new ScribeTrackedSource[]
        {
            new(testProject, """
                <Project Sdk="Microsoft.NET.Sdk">
                  <ItemGroup>
                    <PackageReference Include="xunit" Version="2.9.3" />
                    <ProjectReference Include="../../../src/Corpus/Corpus.csproj" />
                  </ItemGroup>
                </Project>
                """),
            new(testSource, $$"""
                using StrataLint.Engine;
                using Xunit;

                public sealed class UniverseTests
                {
                    [Fact]
                    public void ReadsCompiledDefinitions() { {{testStatement}} }
                }
                """),
            new(productionProject, "<Project Sdk=\"Microsoft.NET.Sdk\" />"),
            new(productionSource, $$"""
                NAMESPACE StrataLint.Engine
                {
                    [AttributeUsage(AttributeTargets.Property | AttributeTargets.Method)]
                    public sealed class CompileTimeInputUniverseAttribute(
                        string prefix,
                        string suffix) : Attribute;

                    public static class Definitions
                    {
                        [CompileTimeInputUniverse("Blueprint/", ".scribe.cs")]
                        public static object All => new();
                    }

                    public static class DefinitionWrapper
                    {
                        {{wrapperMember}}
                    }
                }
                """.Replace("NAMESPACE", "name" + "space", StringComparison.Ordinal)),
        };
        var projectBySource = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [testSource] = testProject,
            [productionSource] = productionProject,
        };
        var context = ScribeProjectCompilationContext.Create(
            tracked,
            projectBySource,
            new HashSet<string>(StringComparer.Ordinal) { testProject });
        return ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(testSource, tracked.Single(file => file.Path == testSource).Content)],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [testSource] = testProject },
            productionAssemblies: context.ProductionAssemblies,
            compilationContext: context);
    }
}
