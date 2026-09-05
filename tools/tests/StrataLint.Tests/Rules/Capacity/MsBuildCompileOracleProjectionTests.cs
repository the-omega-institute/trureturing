using StrataLint.Engine;
using System.Text.Json;

namespace StrataLint.Tests;

public sealed class MsBuildCompileOracleProjectionTests
{
    [Fact]
    public void MaterializeWritesOnlyEffectiveDerivationInputProjection()
    {
        var snapshot = Snapshot(
            ("src/Tracked.cs", "internal sealed class Tracked;\n"),
            ("README.md", "outside projection\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);
        using var checkout = MsBuildCompileOracle.Materialize(projection);

        Assert.Equal(["src/Tracked.cs"], checkout.MaterializedPaths);
    }

    [Fact]
    public void EffectiveProjectionStartsWithExactlyTheDerivationInputSeed()
    {
        var snapshot = Snapshot(
            ("src/App.cs", "internal sealed class App;\n"),
            ("src/App.csproj", Project()),
            ("src/packages.lock.json", "{}\n"),
            ("build/common.props", "<Project />\n"),
            ("README.md", "outside projection\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Sparse, projection.Mode);
        Assert.Equal(
            [
                "build/common.props",
                "src/App.cs",
                "src/App.csproj",
                "src/packages.lock.json",
            ],
            projection.Files.Select(static file => file.Path.Value));
    }

    [Fact]
    public void LiteralImportClosureIncludesPropsTargetsAndFilesOutsideSeed()
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project("<Import Project=\"../build/first.custom\" />")),
            ("build/first.custom", "<Project><Import Project=\"nested.rules\" /></Project>\n"),
            ("build/nested.rules", "<Project />\n"),
            ("build/seed.props", "<Project />\n"),
            ("build/seed.targets", "<Project />\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);
        var paths = projection.Files.Select(static file => file.Path.Value).ToArray();

        Assert.Equal(DerivationInputProjectionMode.Sparse, projection.Mode);
        Assert.Contains("build/first.custom", paths);
        Assert.Contains("build/nested.rules", paths);
        Assert.Contains("build/seed.props", paths);
        Assert.Contains("build/seed.targets", paths);
    }

    [Fact]
    public void LiteralImportClosureStartsFromEveryMsBuildSeedFile()
    {
        var snapshot = Snapshot(
            ("build/seed.props", "<Project><Import Project=\"nested.rules\" /></Project>\n"),
            ("build/nested.rules", "<Project />\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Sparse, projection.Mode);
        Assert.Contains("build/nested.rules", projection.Files.Select(static file => file.Path.Value));
    }

    [Theory]
    [InlineData("$(SomeProp).props")]
    [InlineData("$(BuildRoot)/shared.custom")]
    [InlineData("../build/*.props")]
    public void NonLiteralImportRequiresFullSnapshot(string importPath)
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project($"<Import Project=\"{importPath}\" />")),
            ("build/shared.custom", "<Project />\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Full, projection.Mode);
        Assert.Equal(snapshot.Files.Count, projection.Files.Count);
    }

    [Fact]
    public void DirectoryBuildAndPackagesFilesOnProjectAncestorChainAreIncluded()
    {
        var snapshot = Snapshot(
            ("Directory.Build.props", "<Project />\n"),
            ("Directory.Packages.props", "<Project />\n"),
            ("src/Directory.Build.targets", "<Project />\n"),
            ("src/tests/App.csproj", Project()),
            ("unrelated.txt", "outside projection\n"));

        var paths = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot)
            .Files.Select(static file => file.Path.Value).ToArray();

        Assert.Contains("Directory.Build.props", paths);
        Assert.Contains("Directory.Packages.props", paths);
        Assert.Contains("src/Directory.Build.targets", paths);
        Assert.DoesNotContain("unrelated.txt", paths);
    }

    [Fact]
    public void ExistsConditionOnRepositoryFileOutsideProjectionRequiresFullSnapshot()
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project(
                "<PropertyGroup Condition=\"Exists('../build/enabled.flag')\"><Enabled>true</Enabled></PropertyGroup>")),
            ("build/enabled.flag", "enabled\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Full, projection.Mode);
    }

    [Fact]
    public void ExistsConditionOnRepositoryDirectoryRequiresFullSnapshot()
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project(
                "<PropertyGroup Condition=\"Exists('../build')\"><Enabled>true</Enabled></PropertyGroup>")),
            ("build/enabled.flag", "enabled\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Full, projection.Mode);
    }

    [Fact]
    public void DynamicPropertyInExistsConditionRequiresFullSnapshot()
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project(
                "<PropertyGroup Condition=\"Exists('$(SomeDir)/x.props')\"><Enabled>true</Enabled></PropertyGroup>")));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Full, projection.Mode);
    }

    [Fact]
    public void OrdinaryPropertyReferencesInPropertyBodyAndConditionKeepSparseProjection()
    {
        var snapshot = Snapshot(
            ("Directory.Build.props", """
                <Project>
                  <PropertyGroup Condition="'$(CI)' == 'true'">
                    <WarningsAsErrors>$(WarningsAsErrors);NU1605</WarningsAsErrors>
                  </PropertyGroup>
                </Project>
                """),
            ("src/App.csproj", Project()),
            ("README.md", "outside projection\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Sparse, projection.Mode);
        Assert.Equal(
            ["Directory.Build.props", "src/App.csproj"],
            projection.Files.Select(static file => file.Path.Value));
    }

    [Fact]
    public void OrdinaryPropertyNameContainingExistsKeepsSparseProjection()
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project(
                "<PropertyGroup Condition=\"'$(FileExistsFlag)' == 'true'\"><Enabled>true</Enabled></PropertyGroup>")));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Sparse, projection.Mode);
    }

    [Fact]
    public void PropertyBodyFileReadRequiresFullSnapshot()
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project(
                "<PropertyGroup><Value>$([System.IO.File]::ReadAllText('../config/value.txt'))</Value></PropertyGroup>")),
            ("config/value.txt", "value\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Full, projection.Mode);
    }

    [Fact]
    public void DynamicDirectoryBuildFileNameInGetPathOfFileAboveRequiresFullSnapshot()
    {
        var snapshot = Snapshot(
            ("Directory.Build.Release.props", "<Project />\n"),
            ("src/App.csproj", Project(
                "<Import Project=\"$([MSBuild]::GetPathOfFileAbove('Directory.Build.$(Flavor).props', '$(MSBuildThisFileDirectory)..'))\" />")));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Full, projection.Mode);
    }

    [Fact]
    public void GetPathOfFileAboveLiteralAncestorKeepsSparseProjectionAndIncludesAncestor()
    {
        var snapshot = Snapshot(
            ("Directory.Build.props", "<Project />\n"),
            ("src/tests/App.csproj", Project(
                "<Import Project=\"$([MSBuild]::GetPathOfFileAbove('Directory.Build.props', '$(MSBuildThisFileDirectory)..'))\" />")),
            ("README.md", "outside projection\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Sparse, projection.Mode);
        Assert.Equal(
            ["Directory.Build.props", "src/tests/App.csproj"],
            projection.Files.Select(static file => file.Path.Value));
    }

    [Fact]
    public void GetDirectoryNameOfFileAboveLiteralAncestorKeepsSparseProjectionAndIncludesAncestor()
    {
        var snapshot = Snapshot(
            ("Directory.Build.props", "<Project />\n"),
            ("src/tests/App.csproj", Project(
                "<Import Project=\"$([MSBuild]::GetDirectoryNameOfFileAbove($(MSBuildThisFileDirectory), 'Directory.Build.props'))/Directory.Build.props\" />")),
            ("README.md", "outside projection\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Sparse, projection.Mode);
        Assert.Equal(
            ["Directory.Build.props", "src/tests/App.csproj"],
            projection.Files.Select(static file => file.Path.Value));
    }

    [Fact]
    public void ThisFileDirectoryLiteralItemPathKeepsSparseProjectionAndIncludesFile()
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project(
                "<ItemGroup><AdditionalFiles Include=\"$(MSBuildThisFileDirectory)../config/rules.txt\" /></ItemGroup>")),
            ("config/rules.txt", "rules\n"),
            ("README.md", "outside projection\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Sparse, projection.Mode);
        Assert.Equal(
            ["config/rules.txt", "src/App.csproj"],
            projection.Files.Select(static file => file.Path.Value));
    }

    [Fact]
    public void ThisFileDirectoryExistsOnProjectionFileKeepsSparseProjection()
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project(
                "<PropertyGroup Condition=\"Exists('$(MSBuildThisFileDirectory)marker.props')\"><Enabled>true</Enabled></PropertyGroup>")),
            ("src/marker.props", "<Project />\n"),
            ("README.md", "outside projection\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Sparse, projection.Mode);
        Assert.Equal(
            ["src/App.csproj", "src/marker.props"],
            projection.Files.Select(static file => file.Path.Value));
    }

    [Fact]
    public void CompileCsWildcardKeepsSparseProjectionWhenMatchesAreDerivationSeeds()
    {
        var snapshot = Snapshot(
            ("tools/StrataLint.Scribe/StrataLint.Scribe.csproj", Project(
                "<ItemGroup><Compile Include=\"../../Blueprint/**/*.scribe.cs\" /></ItemGroup>")),
            ("Blueprint/D5/Definition.scribe.cs", "internal sealed class Definition;\n"),
            ("README.md", "outside projection\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Sparse, projection.Mode);
        Assert.Equal(
            [
                "Blueprint/D5/Definition.scribe.cs",
                "tools/StrataLint.Scribe/StrataLint.Scribe.csproj",
            ],
            projection.Files.Select(static file => file.Path.Value));
    }

    [Theory]
    [InlineData("/external/**/*.cs")]
    [InlineData("../../../external/**/*.cs")]
    public void CompileCsWildcardOutsideRepositoryRequiresFullSnapshot(string include)
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project(
                $"<ItemGroup><Compile Include=\"{include}\" /></ItemGroup>")));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Full, projection.Mode);
    }

    [Fact]
    public void CompileDirectoryEnumerationOutsideSeedRequiresFullSnapshot()
    {
        var snapshot = Snapshot(
            ("src/App.csproj", Project(
                "<ItemGroup><Compile Include=\"../generated/**/*.source\" /></ItemGroup>")),
            ("generated/Test.source", "internal sealed class Test;\n"));

        var projection = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);

        Assert.Equal(DerivationInputProjectionMode.Full, projection.Mode);
    }

    [Fact]
    public void SparseAndFullMaterializationProduceCanonicalEquivalentScribeTestMaps()
    {
        const string projectPath = "tools/tests/Synthetic.Tests/Synthetic.Tests.csproj";
        var snapshot = Snapshot(
            (projectPath, Project("<ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup>")),
            ("tools/tests/Synthetic.Tests/ProjectionTests.cs", """
                using Xunit;

                public sealed class ProjectionTests
                {
                    [Fact]
                    public void ReadsOnlyMemory() => Assert.True(true);
                }
                """),
            ("tools/tests/Synthetic.Tests/packages.lock.json", """
                {
                  "version": 1,
                  "dependencies": {
                    "net10.0": {
                      "xunit.extensibility.core": { "type": "Direct", "resolved": "2.9.3" },
                      "xunit.assert": { "type": "Direct", "resolved": "2.9.3" }
                    }
                  }
                }
                """),
            ("README.md", "outside projection\n"));
        var sparse = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);
        var full = EffectiveDerivationInputProjection.Full(snapshot);

        var sparseMap = DeriveMaterialized(snapshot, sparse, projectPath);
        var fullMap = DeriveMaterialized(snapshot, full, projectPath);

        Assert.Equal(Canonicalize(fullMap), Canonicalize(sparseMap));
    }

    private static ScribeTestMap DeriveMaterialized(
        RepositorySnapshot snapshot,
        EffectiveDerivationInputProjection projection,
        string projectPath)
    {
        using var checkout = MsBuildCompileOracle.Materialize(projection);
        var tracked = snapshot.Files.Values
            .Where(static file => ScribeTestMapDeriver.IsDerivationInput(file.Path.Value))
            .Where(static file => file.Path.Value.EndsWith(".cs", StringComparison.Ordinal)
                || file.Path.Value.EndsWith(".csproj", StringComparison.Ordinal)
                || file.Path.Value.EndsWith("packages.lock.json", StringComparison.Ordinal))
            .Select(static file => new ScribeTrackedSource(file.Path.Value, file.Text))
            .ToArray();
        return ScribeTestMapDeriver.DeriveTracked(
            tracked,
            MsBuildCompileOracle.Query(checkout.Root, [projectPath]));
    }

    private static string Canonicalize(ScribeTestMap map) => JsonSerializer.Serialize(new
    {
        Methods = map.Methods.Select(static method => new
        {
            method.PartitionKey,
            method.SourcePath,
            method.Id,
            UnknownReasons = method.UnknownReasons.Select(static reason => reason.ToString()).ToArray(),
        }).ToArray(),
        Unclassified = map.UnclassifiedManagedProjectPaths.ToArray(),
        Orphans = map.OrphanManagedSourcePaths.ToArray(),
        DanglingExemptions = map.DanglingCompileFailProofProjectExemptionPaths.ToArray(),
        CompileFindings = map.CompileQueryFindings.Select(static finding => new
        {
            finding.Path,
            finding.Message,
        }).ToArray(),
    });

    private static string Project(string body = "") =>
        $"<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>{body}</Project>\n";

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(static file =>
                RawRepositoryEntry.FromText(file.Path, file.Text))))).Snapshot;
}
