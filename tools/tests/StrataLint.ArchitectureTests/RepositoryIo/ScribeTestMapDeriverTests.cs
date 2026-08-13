namespace StrataLint.ArchitectureTests;

public sealed class ScribeTestMapDeriverTests
{
    [Fact]
    public void RepositoryMapHasNoUnknownGrowthAndEveryPathIsDeclared()
    {
        var map = ScribeTestMapDeriver.DeriveRepository(RepositoryLayout.FindRoot());

        // Baseline observed on phase 4a branch: 280 methods are still conservative
        // unknowns. Until the parser can resolve them, they must not increase.
        Assert.InRange(
            map.Methods.Count(static method => method.IsUnknown),
            0,
            280);
        Assert.All(
            map.Methods.SelectMany(static method => method.Paths),
            path => Assert.True(
                ScribeTestMapDeriver.IsDeclaredPathAllowed(path),
                $"undeclared repository read path: {path}"));
    }

    [Fact]
    public void DiscoveryMarkerFollowsRepositoryAccessorSource()
    {
        var map = DeriveDiscoveryWithAccessorMarker("File.Exists(Path.Combine(root, \"PROJECT.md\"))");

        Assert.Equal(["PROJECT.md"], Assert.Single(map.Methods).Paths);
    }

    [Fact]
    public void UnparseableDiscoveryMarkerIsUnknownAndSelectedForEveryChange()
    {
        var map = DeriveDiscoveryWithAccessorMarker("File.Exists(Path.Combine(root, markerPath))");

        var method = Assert.Single(map.Methods);
        Assert.True(method.IsUnknown);
        Assert.Contains(method, map.Select(["unrelated.txt"]));
    }

    [Fact]
    public void SensitivityFollowsRepositoryPathLiteralInSource()
    {
        var first = Derive("Golden/one.json");
        var second = Derive("Golden/two.json");

        Assert.Equal(["CLAUDE.md", "Golden/one.json"], first.Methods.Single().Paths);
        Assert.Equal(["CLAUDE.md", "Golden/two.json"], second.Methods.Single().Paths);
    }

    [Fact]
    public void VariablePathIsUnknownAndSelectedForEveryChange()
    {
        const string source = """
            class VariableTests {
              [Fact] public void ReadsVariable() {
                var path = GetPath();
                RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound)
                  .ReadAllText(RepositoryRelativePath.Create(path));
              }
              private string GetPath() => "CLAUDE.md";
            }
            """;

        var map = DeriveSources([new("VariableTests.cs", source)]);

        var method = Assert.Single(map.Methods);
        Assert.Equal(TestMapUnknownReason.VariablePath, Assert.Single(method.UnknownReasons));
        Assert.Contains(method, map.Select(["unrelated.txt"]));
    }

    [Fact]
    public void SingleNamedPathIsNotSelectedForUnrelatedChange()
    {
        var map = Derive("Golden/only.json");

        Assert.Empty(map.Select(["Golden/other.json"]));
        Assert.Single(map.Select(["Golden/only.json"]));
    }

    [Fact]
    public void DiscoveryDirectorySelectsChangesBelowThatDirectory()
    {
        const string source = """
            class DirectoryTests {
              [Fact] public void Discovers() => RepositoryAccessor.Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound);
            }
            """;
        var map = DeriveSources([new("DirectoryTests.cs", source)]);

        Assert.Single(map.Select(["Blueprint/Nested/document.scribe.cs"]));
    }

    [Fact]
    public void ReachableHelpersContributePathsAndUnknownReasons()
    {
        const string source = """
            class SampleTests {
              [Fact] public void A() => Read("A.json");
              [Fact] public void B() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).ReadAllBytes(RepositoryRelativePath.Create("B.json"));
              [Theory] public void C() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).FileExists(RepositoryRelativePath.Create("C.json"));
              [Fact] public void D() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).CopyTo(RepositoryRelativePath.Create("D.json"), null);
              [Fact] public void E() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).EnumerateFiles(RepositoryRelativePath.Create("E"), "*.json");
              private void Read(string ignored) => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).ReadAllText(RepositoryRelativePath.Create("A.json"));
            }
            """;

        var map = DeriveSources([new("SampleTests.cs", source)]);

        Assert.Equal(["A.json", "CLAUDE.md"], map.Methods.Single(method => method.Id.EndsWith(".A", StringComparison.Ordinal)).Paths);
        Assert.Equal(["B.json", "CLAUDE.md"], map.Methods.Single(method => method.Id.EndsWith(".B", StringComparison.Ordinal)).Paths);
        Assert.Equal(["C.json", "CLAUDE.md"], map.Methods.Single(method => method.Id.EndsWith(".C", StringComparison.Ordinal)).Paths);
        Assert.Equal(["CLAUDE.md", "D.json"], map.Methods.Single(method => method.Id.EndsWith(".D", StringComparison.Ordinal)).Paths);
        var enumerating = map.Methods.Single(method => method.Id.EndsWith(".E", StringComparison.Ordinal));
        Assert.Equal(["CLAUDE.md", "E"], enumerating.Paths);
        Assert.Equal(TestMapUnknownReason.DirectoryEnumeration, Assert.Single(enumerating.UnknownReasons));
    }

    private static ScribeTestMap Derive(string path)
    {
        var source = $$"""
            class LiteralTests {
              [Fact] public void ReadsLiteral() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound)
                .ReadAllText(RepositoryRelativePath.Create("{{path}}"));
            }
            """;
        return DeriveSources([new("LiteralTests.cs", source)]);
    }

    private static ScribeTestMap DeriveDiscoveryWithAccessorMarker(string markerExpression)
    {
        const string testSource = """
            class DiscoveryTests {
              [Fact] public void Discovers() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound);
            }
            """;
        var accessorSource = $$"""
            class RepositoryAccessor {
              private static bool Matches(string root, RepositoryRootCriterion criterion) => criterion switch {
                RepositoryRootCriterion.ClaudeDirectoryNotFound => {{markerExpression}},
                _ => false,
              };
            }
            """;

        return ScribeTestMapDeriver.DeriveSources(
            [new("DiscoveryTests.cs", testSource), new("Support/RepositoryAccessor.cs", accessorSource)],
            []);
    }

    private static ScribeTestMap DeriveSources(IEnumerable<TestMapSource> sources)
    {
        const string accessorSource = """
            class RepositoryAccessor {
              private static bool Matches(string root, RepositoryRootCriterion criterion) => criterion switch {
                RepositoryRootCriterion.ClaudeDirectoryNotFound => File.Exists(Path.Combine(root, "CLAUDE.md")),
                RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound =>
                  File.Exists(Path.Combine(root, "global.json")) && Directory.Exists(Path.Combine(root, "Blueprint")),
                _ => false,
              };
            }
            """;
        return ScribeTestMapDeriver.DeriveSources(
            sources.Append(new("Support/RepositoryAccessor.cs", accessorSource)),
            []);
    }
}
