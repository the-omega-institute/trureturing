using Microsoft.CodeAnalysis;
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
    public void DerivedFactAttributeConstructorCalledMethodThatAssignsSkipIsExcludedFromBasePlan()
    {
        const string source = "tools/tests/Synthetic.Tests/CalledSkipTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class CalledSkipFactAttribute : FactAttribute
                {
                    public CalledSkipFactAttribute()
                    {
                        Disable();
                    }

                    private void Disable()
                    {
                        this.Skip = "the constructor reaches this method";
                    }
                }

                public sealed class CalledSkipTests
                {
                    [CalledSkipFact]
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
    public void DerivedFactAttributeHiddenSkipPropertyRemainsInBasePlan()
    {
        const string source = "tools/tests/Synthetic.Tests/HiddenSkipTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class HiddenSkipFactAttribute : FactAttribute
                {
                    public new string? Skip { get; set; }

                    public HiddenSkipFactAttribute()
                    {
                        Skip = "this property does not control xUnit skipping";
                    }
                }

                public sealed class HiddenSkipTests
                {
                    [HiddenSkipFact]
                    public void StillRuns() { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project });

        Assert.False(Assert.Single(map.Methods).IsStaticallySkipped);
        var planned = Assert.Single(EngineeringTestPlanPolicy.BaseTests(map, null));
        Assert.Equal("HiddenSkipTests.StillRuns", planned.Id);
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
                    public override string? Skip { get; set; } =
                        "runtime prerequisite is absent";
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
    public void OtherObjectSkipFactAttributeRemainsInBasePlan()
    {
        const string source = "tools/tests/Synthetic.Tests/OtherObjectSkipTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class OtherObjectSkipFactAttribute : FactAttribute
                {
                    private readonly FactAttribute other = new();

                    public OtherObjectSkipFactAttribute()
                    {
                        other.Skip = "does not skip this attribute";
                    }
                }

                public sealed class OtherObjectSkipTests
                {
                    [OtherObjectSkipFact]
                    public void StillRuns() { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project });

        Assert.False(Assert.Single(map.Methods).IsStaticallySkipped);
        var planned = Assert.Single(EngineeringTestPlanPolicy.BaseTests(map, null));
        Assert.Equal("OtherObjectSkipTests.StillRuns", planned.Id);
    }

    [Fact]
    public void SkipAssignmentInUncalledMethodRemainsInBasePlan()
    {
        const string source = "tools/tests/Synthetic.Tests/UncalledSkipTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class UncalledSkipFactAttribute : FactAttribute
                {
                    private void Disable()
                    {
                        Skip = "the constructor never calls this method";
                    }
                }

                public sealed class UncalledSkipTests
                {
                    [UncalledSkipFact]
                    public void StillRuns() { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project });

        Assert.False(Assert.Single(map.Methods).IsStaticallySkipped);
        var planned = Assert.Single(EngineeringTestPlanPolicy.BaseTests(map, null));
        Assert.Equal("UncalledSkipTests.StillRuns", planned.Id);
    }

    [Fact]
    public void NullSkipAssignmentRemainsInBasePlan()
    {
        const string source = "tools/tests/Synthetic.Tests/NullSkipTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class NullSkipFactAttribute : FactAttribute
                {
                    public NullSkipFactAttribute()
                    {
                        Skip = null;
                    }
                }

                public sealed class NullSkipTests
                {
                    [NullSkipFact]
                    public void StillRuns() { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project });

        Assert.False(Assert.Single(map.Methods).IsStaticallySkipped);
        var planned = Assert.Single(EngineeringTestPlanPolicy.BaseTests(map, null));
        Assert.Equal("NullSkipTests.StillRuns", planned.Id);
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

    [Fact]
    public void MetadataOnlyDerivedFactAttributeRemainsInBasePlan()
    {
        const string source = "tools/tests/Synthetic.Tests/ExternalFactTests.cs";
        const string project = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        MetadataReference[] metadataReferences =
        [
            MetadataReference.CreateFromFile(typeof(FactAttribute).Assembly.Location),
            MetadataReference.CreateFromFile(typeof(MetadataOnlySkipFactAttribute).Assembly.Location),
        ];
        var map = ScribeTestMapDeriver.DeriveSources(
            [new TestMapSource(source, """
                public sealed class ExternalFactTests
                {
                    [StrataLint.Engine.Tests.MetadataOnlySkipFact]
                    public void StillRunsBecauseExternalPolarityIsUnknown() { }
                }
                """, "Synthetic.Tests")],
            [],
            compileProjectBySourcePath:
                new Dictionary<string, string>(StringComparer.Ordinal) { [source] = project },
            syntheticXunitMetadataReferences: metadataReferences);

        Assert.False(Assert.Single(map.Methods).IsStaticallySkipped);
        var planned = Assert.Single(EngineeringTestPlanPolicy.BaseTests(map, null));
        Assert.Equal(
            "ExternalFactTests.StillRunsBecauseExternalPolarityIsUnknown",
            planned.Id);
    }
}

public sealed class MetadataOnlySkipFactAttribute : FactAttribute
{
    public MetadataOnlySkipFactAttribute()
    {
        Skip = "metadata-only constructor body is deliberately unavailable to the binder";
    }
}
