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
    public void CompileTimeInputUniverseFactIsSelectedOnlyForMatchingNewCompileInput()
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

        var scribePlan = EngineeringTestPlanPolicy.Evaluate(
            ["Blueprint/D5/S3/NewDefinition.scribe.cs"],
            map);
        var projectionPlan = EngineeringTestPlanPolicy.Evaluate(
            ["Blueprint/D5/S3/NewDefinition.md"],
            map);

        var selected = Assert.Single(scribePlan.Tests);
        Assert.Equal(EngineeringTestPlanKind.Selected, scribePlan.Kind);
        Assert.Equal("UniverseTests.ReadsCompiledDefinitions", selected.Id);
        Assert.Equal(EngineeringSelectedTestReason.DeclaredInput, selected.Reason);
        Assert.Equal(EngineeringTestPlanKind.None, projectionPlan.Kind);
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
        Assert.True(Assert.Single(map.Methods).IsStaticallySkipped);

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

    [Fact]
    public void EnvironmentConditionalFactIsNotAProtectedBaseBlockingExpectation()
    {
        const string source = "tools/tests/Synthetic.Tests/ConditionalTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class ConditionalTests
                {
                    [LiveReportFact]
                    public void RequiresLiveReport() { }

                    [AlwaysFact]
                    public void AlwaysRuns() { }

                    private sealed class LiveReportFactAttribute : FactAttribute
                    {
                        public LiveReportFactAttribute()
                        {
                            if (Environment.GetEnvironmentVariable("LIVE_REPORT") is null)
                                Skip = "Live report is absent.";
                        }
                    }

                    private sealed class AlwaysFactAttribute : FactAttribute { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project });
        var assemblies = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [project] = "Synthetic.Custom.Tests",
        };

        var planned = EngineeringTestPlanPolicy.BaseTests(map, assemblies);
        var sourceIdentities = EngineeringTestPlanPolicy.SourceIdentities(map, assemblies);

        Assert.True(map.Methods.Single(static method =>
            method.Id == "ConditionalTests.RequiresLiveReport").IsDiscoveryConditional);
        Assert.False(map.Methods.Single(static method =>
            method.Id == "ConditionalTests.AlwaysRuns").IsDiscoveryConditional);
        Assert.Equal(["ConditionalTests.AlwaysRuns"], planned.Select(static test => test.Id));
        Assert.Contains(
            sourceIdentities,
            static test => test.Id == "ConditionalTests.RequiresLiveReport");
    }
}
