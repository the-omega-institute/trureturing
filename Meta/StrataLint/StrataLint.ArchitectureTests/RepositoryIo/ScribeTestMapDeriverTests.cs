namespace StrataLint.ArchitectureTests;

public sealed class ScribeTestMapDeriverTests
{
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

        var map = ScribeTestMapDeriver.DeriveSources([new("VariableTests.cs", source)], []);

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
        var map = ScribeTestMapDeriver.DeriveSources([new("DirectoryTests.cs", source)], []);

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

        var map = ScribeTestMapDeriver.DeriveSources([new("SampleTests.cs", source)], []);

        Assert.Equal(["A.json", "CLAUDE.md"], map.Methods.Single(method => method.Id.EndsWith(".A", StringComparison.Ordinal)).Paths);
        Assert.Equal(["B.json", "CLAUDE.md"], map.Methods.Single(method => method.Id.EndsWith(".B", StringComparison.Ordinal)).Paths);
        Assert.Equal(["C.json", "CLAUDE.md"], map.Methods.Single(method => method.Id.EndsWith(".C", StringComparison.Ordinal)).Paths);
        Assert.Equal(["CLAUDE.md", "D.json"], map.Methods.Single(method => method.Id.EndsWith(".D", StringComparison.Ordinal)).Paths);
        Assert.Equal(TestMapUnknownReason.DirectoryEnumeration,
            Assert.Single(map.Methods.Single(method => method.Id.EndsWith(".E", StringComparison.Ordinal)).UnknownReasons));
    }

    private static ScribeTestMap Derive(string path)
    {
        var source = $$"""
            class LiteralTests {
              [Fact] public void ReadsLiteral() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound)
                .ReadAllText(RepositoryRelativePath.Create("{{path}}"));
            }
            """;
        return ScribeTestMapDeriver.DeriveSources([new("LiteralTests.cs", source)], []);
    }
}
