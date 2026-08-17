namespace StrataLint.ArchitectureTests;

public sealed class ScribeTestMapDeriverTests
{
    [Fact]
    public void RepositoryMapHasNoUnknownGrowthAndEveryPathIsDeclared()
    {
        var map = ScribeTestMapDeriver.DeriveRepository(RepositoryLayout.FindRoot());

        Assert.Equal(280, ScribeUnknownDebtPolicy.UnknownDebtLimit);
        Assert.Equal(281, ScribeUnknownDebtPolicy.UnknownDebtToleranceLimit);
        Assert.Empty(ScribeUnknownDebtPolicy.InspectCurrent(map));
        Assert.All(
            map.Methods.SelectMany(static method => method.Paths),
            path => Assert.True(
                ScribeTestMapDeriver.IsDeclaredPathAllowed(path),
                $"undeclared repository read path: {path}"));
    }

    [Fact]
    public void UnknownDebtPartitionsAreDerivedFromXunitProjectInputs()
    {
        const string xunitProject =
            "<Project><ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup></Project>";
        const string compileProof = "<Project />";

        var partitions = ScribeTestMapDeriver.DeriveProjectPartitions(
        [
            ("tools/tests/Alpha.Tests/Alpha.Tests.csproj", xunitProject),
            ("tools/tests/NewPartition.Tests/NewPartition.Tests.csproj", xunitProject),
            ("tools/tests/CompileProof/CompileProof.csproj", compileProof),
        ]);

        Assert.Equal(
            ["tools/tests/Alpha.Tests", "tools/tests/NewPartition.Tests"],
            partitions.Select(static partition => partition.Key));
    }

    [Fact]
    public void UnknownDebtBaselineSchemaV1GroupsMethodsByDerivedPartitionKey()
    {
        const string source = """
            class DebtTests {
              [Fact] public void ReadsVariable() {
                var path = GetPath();
                File.ReadAllText(path);
              }
            }
            """;
        var map = ScribeTestMapDeriver.DeriveSources(
        [
            new("tools/tests/Alpha.Tests/DebtTests.cs", source, "tools/tests/Alpha.Tests"),
            new("tools/tests/Beta.Tests/DebtTests.cs", source, "tools/tests/Beta.Tests"),
        ],
        []);

        var baseline = ScribeUnknownDebtBaselineV1.Create(map);

        Assert.Equal(ScribeUnknownDebtBaselineV1.CurrentSchemaVersion, baseline.SchemaVersion);
        Assert.Equal(2, baseline.UnknownCount);
        Assert.Equal(
            ["tools/tests/Alpha.Tests", "tools/tests/Beta.Tests"],
            baseline.Partitions.Keys);
    }

    [Fact]
    public void UnknownDebtPastToleranceIsDetectedRepositoryWide()
    {
        var methods = string.Join('\n', Enumerable.Range(
                0,
                ScribeUnknownDebtPolicy.UnknownDebtToleranceLimit + 1)
            .Select(static index =>
                $"[Fact] public void Debt{index:000}() {{ var path = GetPath(); File.ReadAllText(path); }}"));
        var map = ScribeTestMapDeriver.DeriveSources(
        [
            new(
                "tools/tests/Synthetic.Tests/DebtTests.cs",
                $"class DebtTests {{\n{methods}\n}}",
                "tools/tests/Synthetic.Tests"),
        ],
        []);

        var finding = Assert.Single(ScribeUnknownDebtPolicy.InspectCurrent(map));

        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Contains("repository tolerance 281", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DiscoveryMarkerFollowsRepositoryAccessorSource()
    {
        var map = DeriveDiscoveryWithAccessorMarker("File.Exists(Path.Combine(root, \"PROJECT.md\"))");

        Assert.Equal(["PROJECT.md"], Assert.Single(map.Methods).Paths);
    }

    [Fact]
    public void UnparseableDiscoveryMarkerIsUnknown()
    {
        var map = DeriveDiscoveryWithAccessorMarker("File.Exists(Path.Combine(root, markerPath))");

        var method = Assert.Single(map.Methods);
        Assert.True(method.IsUnknown);
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
    public void VariablePathIsUnknown()
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
    }

    [Fact]
    public void DiscoveryDirectoryContributesBothMarkersToPaths()
    {
        const string source = """
            class DirectoryTests {
              [Fact] public void Discovers() => RepositoryAccessor.Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound);
            }
            """;
        var map = DeriveSources([new("DirectoryTests.cs", source)]);

        Assert.Equal(["Blueprint", "global.json"], Assert.Single(map.Methods).Paths);
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
