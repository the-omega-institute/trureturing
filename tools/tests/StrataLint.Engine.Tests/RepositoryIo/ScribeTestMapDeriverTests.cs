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
    public void DerivedFactAttributeConstructorThatAssignsSkipIsExcludedFromBasePlan()
    {
        const string source = "tools/tests/Synthetic.Tests/ConditionalTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class ConditionalFactAttribute : FactAttribute
                {
                    public ConditionalFactAttribute()
                    {
                        Skip = "runtime prerequisite is absent";
                    }
                }

                public sealed class ConditionalTests
                {
                    [ConditionalFact]
                    public void RequiresRuntimePrerequisite() { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project });

        Assert.True(Assert.Single(map.Methods).IsStaticallySkipped);
        Assert.Empty(EngineeringTestPlanPolicy.BaseTests(map, null));
    }

    [Fact]
    public void DerivedFactAttributeSkipPropertyInitializerIsExcludedFromBasePlan()
    {
        const string source = "tools/tests/Synthetic.Tests/PropertyInitializerTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class InitializedFactAttribute : FactAttribute
                {
                    public new string? Skip { get; } = "runtime prerequisite is absent";
                }

                public sealed class PropertyInitializerTests
                {
                    [InitializedFact]
                    public void RequiresRuntimePrerequisite() { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project });

        Assert.True(Assert.Single(map.Methods).IsStaticallySkipped);
        Assert.Empty(EngineeringTestPlanPolicy.BaseTests(map, null));
    }

    [Fact]
    public void DerivedFactAttributeFieldInitializerThatAssignsSkipIsExcludedFromBasePlan()
    {
        const string source = "tools/tests/Synthetic.Tests/FieldInitializerTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class InitializedFactAttribute : FactAttribute
                {
                    private readonly FactAttribute configured = new() {
                        Skip = "runtime prerequisite is absent"
                    };
                }

                public sealed class FieldInitializerTests
                {
                    [InitializedFact]
                    public void RequiresRuntimePrerequisite() { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project });

        Assert.True(Assert.Single(map.Methods).IsStaticallySkipped);
        Assert.Empty(EngineeringTestPlanPolicy.BaseTests(map, null));
    }

    [Fact]
    public void DerivedFactAttributeWithoutSkipAssignmentRemainsInBasePlan()
    {
        const string source = "tools/tests/Synthetic.Tests/AlwaysRunsTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class AlwaysRunsFactAttribute : FactAttribute
                {
                    public string Category { get; } = "always-runs";
                }

                public sealed class AlwaysRunsTests
                {
                    [AlwaysRunsFact]
                    public void AlwaysRuns() { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project });

        Assert.False(Assert.Single(map.Methods).IsStaticallySkipped);
        var planned = Assert.Single(EngineeringTestPlanPolicy.BaseTests(map, null));
        Assert.Equal("AlwaysRunsTests.AlwaysRuns", planned.Id);
    }
}
