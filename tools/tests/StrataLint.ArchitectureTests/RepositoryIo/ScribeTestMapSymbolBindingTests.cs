namespace StrataLint.ArchitectureTests;

public sealed class ScribeTestMapSymbolBindingTests
{
    [Fact]
    public void ExactOverloadBindingFollowsOnlyTheSelectedSourceMethod()
    {
        const string source = """
            class OverloadTests {
              [Fact] public void SelectsInteger() => Parse(1);
              private static void Parse(int value) => File.ReadAllText(
                Path.Combine(RepositoryLayout.FindRoot(), "D5", "selected.lean"));
              private static void Parse(string value) {
                var path = GetPath();
                File.ReadAllText(path);
              }
              private static string GetPath() => "D5/not-selected.lean";
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal(["D5/selected.lean"], method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void AliasQualifiedGenericNestedReceiverBindsAcrossTypes()
    {
        const string source = """
            using ReaderAlias = Support.Reader<int>.Nested;
            class QualifiedTests {
              [Fact] public void Reads() => ReaderAlias.Read();
            }
            static class Support {
              internal static class Reader<T> {
                internal static class Nested {
                  internal static void Read() => File.ReadAllText(
                    Path.Combine(RepositoryLayout.FindRoot(), "D5", "qualified.lean"));
                }
              }
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal(["D5/qualified.lean"], method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void InheritedExtensionAndMethodGroupTargetsAreFollowed()
    {
        const string source = """
            class BindingTests : BindingBase {
              [Fact] public void Reads() {
                ReadBase();
                1.ReadExtension();
                Array.ForEach(new[] { 1 }, BindingReaders.ReadGroup);
              }
            }
            class BindingBase {
              protected static void ReadBase() => File.ReadAllText(
                Path.Combine(RepositoryLayout.FindRoot(), "D5", "base.lean"));
            }
            static class BindingReaders {
              internal static void ReadExtension(this int value) => File.ReadAllText(
                Path.Combine(RepositoryLayout.FindRoot(), "D5", "extension.lean"));
              internal static void ReadGroup(int value) => File.ReadAllText(
                Path.Combine(RepositoryLayout.FindRoot(), "D5", "group.lean"));
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal(["D5/base.lean", "D5/extension.lean", "D5/group.lean"], method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void CrossFilePartialHelperUsesItsBoundProjectSymbol()
    {
        var map = ScribeTestMapDeriverTests.DeriveSources(
        [
            new("PartialTests.cs", """
                partial class PartialTests {
                  [Fact] public void Reads() => ReadHelper();
                }
                """),
            new("PartialTests.Helpers.cs", """
                partial class PartialTests {
                  private static void ReadHelper() => File.ReadAllText(
                    Path.Combine(RepositoryLayout.FindRoot(), "D5", "partial.lean"));
                }
                """),
        ]);

        var method = Assert.Single(map.Methods);

        Assert.Equal(["D5/partial.lean"], method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void NameofDoesNotCreateACallEdge()
    {
        const string source = """
            class NameofTests {
              [Fact] public void Reads() {
                _ = nameof(UnreachableVariableRead);
                File.ReadAllText(Path.Combine(RepositoryLayout.FindRoot(), "D5", "named.lean"));
              }
              private static void UnreachableVariableRead() {
                var path = GetPath();
                File.ReadAllText(path);
              }
              private static string GetPath() => "D5/unreachable.lean";
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal(["D5/named.lean"], method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void BoundMetadataInvocationDoesNotCreateUnknownDebt()
    {
        const string source = """
            class MetadataTests {
              [Fact] public void Parses() {
                _ = int.Parse("1");
                File.ReadAllText(Path.Combine(RepositoryLayout.FindRoot(), "D5", "metadata.lean"));
              }
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal(["D5/metadata.lean"], method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void BoundScratchPathProvenanceDoesNotCreateUnknownDebt()
    {
        const string source = """
            class OutputTests {
              [Fact] public void ReadsGeneratedOutput() {
                var output = new OutputDirectory(new ScratchSpace());
                OutputReader.Read(output, "result.json");
                OutputReader.Snapshot(output);
              }
            }
            sealed class ScratchSpace {
              private string Root { get; } = Directory.CreateTempSubdirectory().FullName;
              internal string CreateDirectory() {
                var path = Path.Combine(Root, Guid.NewGuid().ToString("N"));
                Directory.CreateDirectory(path);
                return path;
              }
            }
            sealed class OutputDirectory {
              internal OutputDirectory(ScratchSpace scratch) => Path = scratch.CreateDirectory();
              internal string Path { get; }
            }
            static class OutputReader {
              internal static byte[] Read(OutputDirectory output, string fileName) =>
                File.ReadAllBytes(Path.Combine(output.Path, fileName));
              internal static byte[][] Snapshot(OutputDirectory output) =>
                Directory.EnumerateFiles(output.Path)
                  .Order(StringComparer.Ordinal)
                  .Select(path => File.ReadAllBytes(path))
                  .ToArray();
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Empty(method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Theory]
    [InlineData("Missing();")]
    [InlineData("Choose(default);")]
    [InlineData("dynamic value = new object(); value.Missing();")]
    public void UnresolvedAmbiguousAndDynamicInvocationsFailClosed(string statement)
    {
        var source = $$"""
            class UnboundTests {
              [Fact] public void Executes() { {{statement}} }
              private static void Choose(string value) { }
              private static void Choose(Uri value) { }
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal(TestMapUnknownReason.Other, Assert.Single(method.UnknownReasons));
    }

    [Fact]
    public void DerivedFactAttributeAndItsConstructorAreCallableRoots()
    {
        const string source = """
            class DerivedFactTests {
              [LiveReportFact] public void Reads() { }
              private sealed class LiveReportFactAttribute : FactAttribute {
                public LiveReportFactAttribute() {
                  if (Environment.GetEnvironmentVariable("LIVE_REPORT") != "1")
                    Skip = "live report is absent";
                  File.ReadAllText(Path.Combine(
                    RepositoryLayout.FindRoot(), "D5", "attribute.lean"));
                }
              }
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal("DerivedFactTests.Reads", method.Id);
        Assert.Equal(["D5/attribute.lean"], method.Paths);
        Assert.Equal(["live report is absent"], method.RuntimeConditionalSkipReasons);
        var contract = Assert.Single(method.RuntimeConditionalSkipContracts);
        Assert.Equal(64, contract.Length);
        var changedCondition = Assert.Single(Derive(source.Replace("!= \"1\"", "== \"1\"", StringComparison.Ordinal)).Methods);
        Assert.NotEqual(contract, Assert.Single(changedCondition.RuntimeConditionalSkipContracts));
    }

    [Fact]
    public void ConstructorsAccessorsAndLocalFunctionsAreInTheClosure()
    {
        const string source = """
            class CallableTests {
              [Fact] public void Reads() {
                var reader = new Reader();
                _ = reader.Value;
                void ReadLocal() => File.ReadAllText(
                  Path.Combine(RepositoryLayout.FindRoot(), "D5", "local.lean"));
                ReadLocal();
              }
              private sealed class Reader {
                internal Reader() => File.ReadAllText(
                  Path.Combine(RepositoryLayout.FindRoot(), "D5", "constructor.lean"));
                internal string Value {
                  get {
                    File.ReadAllText(Path.Combine(RepositoryLayout.FindRoot(), "D5", "accessor.lean"));
                    return string.Empty;
                  }
                }
              }
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal(
            ["D5/accessor.lean", "D5/constructor.lean", "D5/local.lean"],
            method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void ConstructorRootAliasAndBoundConstantProduceAnExactPath()
    {
        const string source = """
            static class RepositoryPaths {
              internal const string Rules = "Meta/rules.toml";
            }
            class RootAliasTests {
              [Fact] public void Reads() => _ = new Reader();
              private sealed class Reader {
                internal Reader() {
                  var root = RepositoryLayout.FindRoot();
                  File.ReadAllText(Path.Combine(root, RepositoryPaths.Rules));
                }
              }
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal(["Meta/rules.toml"], method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void XunitFixtureImplicitConstructorAndInitializerAreCallableRoots()
    {
        const string source = """
            class FixtureTests(FixtureTests.RepositoryFixture fixture) : IClassFixture<FixtureTests.RepositoryFixture> {
              private readonly string value = fixture.Value;
              [Fact] public void Reads() { _ = value; }
              public sealed class RepositoryFixture {
                internal string Value { get; } = Read();
                private static string Read() {
                  File.ReadAllText(Path.Combine(RepositoryLayout.FindRoot(), "D5", "fixture.lean"));
                  return string.Empty;
                }
              }
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal(["D5/fixture.lean"], method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void SameNamedHelpersInDifferentProjectPartitionsDoNotCollide()
    {
        const string template = """
            class PartitionTests {
              [Fact] public void Reads() => Read();
              private static void Read() => File.ReadAllText(
                Path.Combine(RepositoryLayout.FindRoot(), "D5", "__PATH__.lean"));
            }
            """;
        var map = ScribeTestMapDeriver.DeriveSources(
        [
            new("Alpha/PartitionTests.cs", template.Replace("__PATH__", "alpha", StringComparison.Ordinal), "Alpha"),
            new("Beta/PartitionTests.cs", template.Replace("__PATH__", "beta", StringComparison.Ordinal), "Beta"),
        ],
        []);

        Assert.Equal(["D5/alpha.lean"], map.Methods.Single(method => method.PartitionKey == "Alpha").Paths);
        Assert.Equal(["D5/beta.lean"], map.Methods.Single(method => method.PartitionKey == "Beta").Paths);
        Assert.All(map.Methods, static method => Assert.False(method.IsUnknown));
    }

    [Fact]
    public void ReferencedTestProjectHelperUsesItsBoundSourceSymbol()
    {
        const string project = """
            <Project Sdk="Microsoft.NET.Sdk">
              <ItemGroup><PackageReference Include="xunit" Version="2.9.3" /></ItemGroup>
            </Project>
            """;
        var snapshot = ScribeTestMapDeriverTests.Snapshot(
            ("tools/tests/Shared.Tests/Shared.Tests.csproj", project),
            ("tools/tests/Shared.Tests/SharedReader.cs", "using System.IO;\n"
                + "namespace " + "Shared;\n"
                + "internal static class RepositoryLayout {\n"
                + "  internal static string FindRoot() => string.Empty;\n"
                + "}\n"
                + "public static class SharedReader {\n"
                + "  public static void Read() => File.ReadAllText(\n"
                + "    Path.Combine(RepositoryLayout.FindRoot(), \"D5\", \"shared.lean\"));\n"
                + "}\n"),
            ("tools/tests/Consumer.Tests/Consumer.Tests.csproj", project.Replace(
                "</Project>",
                "<ItemGroup><ProjectReference Include=\"../Shared.Tests/Shared.Tests.csproj\" /></ItemGroup></Project>",
                StringComparison.Ordinal)),
            ("tools/tests/Consumer.Tests/ConsumerTests.cs", """
                using Shared;
                using Xunit;
                public class ConsumerTests {
                  [Fact] public void Reads() {
                    Assert.True(true);
                    SharedReader.Read();
                  }
                }
                """));

        var method = Assert.Single(
            ScribeTestMapDeriver.DeriveSnapshot(snapshot).Methods,
            static method => method.Id == "ConsumerTests.Reads");

        Assert.Equal(["D5/shared.lean"], method.Paths);
        Assert.False(method.IsUnknown, string.Join(',', method.UnknownReasons));
    }

    [Fact]
    public void MissingLockedXunitMetadataDegradesEveryProjectTestWithANamedReceipt()
    {
        const string projectPath = "tools/tests/MissingMetadata.Tests/MissingMetadata.Tests.csproj";
        var snapshot = MetadataSnapshot(
            projectPath,
            MissingXunitLock,
            """
            using Xunit;
            public sealed class MissingMetadataTests {
              [Fact] public void DirectFact() { }
              [DerivedFact] public void DerivedFact() { }
              private sealed class DerivedFactAttribute : FactAttribute { }
            }
            """);

        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot);
        var tests = map.Methods.Where(static method =>
            method.Id.StartsWith("MissingMetadataTests.", StringComparison.Ordinal)).ToArray();
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["D5/metadata-unavailable.lean"],
            map,
            new HashSet<string>(StringComparer.Ordinal),
            assemblyByProject: new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [projectPath] = "MissingMetadata.Tests",
            });

        Assert.Equal(2, tests.Length);
        Assert.All(tests, static method => Assert.True(method.IsUnknown));
        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Equal(2, plan.Tests.Length);
        Assert.All(plan.Tests, test =>
        {
            Assert.Equal(EngineeringSelectedTestReason.UnknownInput, test.Reason);
            Assert.Contains(projectPath, test.Detail, StringComparison.Ordinal);
            Assert.Contains("xUnit compile assets are unavailable", test.Detail, StringComparison.Ordinal);
        });
        Assert.Contains(projectPath, plan.Reason, StringComparison.Ordinal);

        var invalidLock = Assert.Throws<InvalidOperationException>(() =>
            ScribeTestMapDeriver.DeriveSnapshot(MetadataSnapshot(
                projectPath,
                IncompleteXunitLock,
                "using Xunit; public sealed class InvalidLockTests { [Fact] public void Fact() { } }")));
        Assert.Contains("does not resolve metadata providers", invalidLock.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AvailableXunitMetadataKeepsExactSymbolBindingEnabled()
    {
        const string projectPath = "tools/tests/AvailableMetadata.Tests/AvailableMetadata.Tests.csproj";
        var snapshot = MetadataSnapshot(
            projectPath,
            packageLock: null,
            """
            using System.IO;
            using Xunit;
            public static class RepositoryLayout {
              public static string FindRoot() => string.Empty;
            }
            public sealed class AvailableMetadataTests {
              [Fact] public void ExactFact() => File.ReadAllText(
                Path.Combine(RepositoryLayout.FindRoot(), "D5", "exact-metadata.lean"));
            }
            """);

        var method = Assert.Single(
            ScribeTestMapDeriver.DeriveSnapshot(snapshot).Methods,
            static method => method.Id == "AvailableMetadataTests.ExactFact");

        Assert.Equal(["D5/exact-metadata.lean"], method.Paths);
        Assert.False(method.IsUnknown, string.Join(',', method.UnknownReasons));
    }

    [Fact]
    public void ExistingKnownIdentityThatBecomesUnknownIsBaselineMigrationNotNewIdentityDebt()
    {
        const string known = """
            class MigrationTests {
              [Fact] public void Existing() => File.ReadAllText(
                Path.Combine(RepositoryLayout.FindRoot(), "D5", "known.lean"));
            }
            """;
        const string unknown = """
            class MigrationTests {
              [Fact] public void Existing() { Missing(); }
            }
            """;
        var forkPoint = Derive(known);
        var current = Derive(unknown);

        Assert.Empty(ScribeUnknownDebtPolicy.Evaluate(current, forkPoint));
    }

    [Fact]
    public void RepositoryMapIncludesDerivedFactsAndRetiredLedgerFixtureClosure()
    {
        var map = DeriveDeclaredRepositoryMap();
        var expectedLivePaths = new Dictionary<string, string[]>(StringComparer.Ordinal)
        {
            ["DocumentDiscoveryTests.GeneratedDocumentGraphMatchesFormalTruth"] =
            [
                ".lake/build/stratalint/raw-lean-report.json",
                ".lake/build/stratalint/raw-lean-report.json.materials.zip",
                "Blueprint",
                "global.json",
            ],
            ["StatementProjectionPilotTests.LiveReportMatchesPinnedFixtureWhenAvailable"] =
            [
                ".lake/build/stratalint/raw-lean-report.json",
                ".lake/build/stratalint/raw-lean-report.json.materials.zip",
                "lakefile.toml",
            ],
            ["StatementProjectionPilotTests.NonTheoremDeclarationsAreUnprojectableWhenTheReportIsAvailable"] =
            [
                ".lake/build/stratalint/raw-lean-report.json",
                ".lake/build/stratalint/raw-lean-report.json.materials.zip",
                "lakefile.toml",
            ],
        };

        foreach (var (id, paths) in expectedLivePaths)
        {
            var matches = map.Methods.Where(method => method.Id == id).ToArray();
            Assert.True(
                matches.Length == 1,
                $"{id}: source peers are {string.Join(", ", map.Methods.Where(method => id.StartsWith(method.Id.Split('.')[0], StringComparison.Ordinal)).Select(static method => method.Id))}");
            Assert.Equal(paths, matches[0].Paths);
            Assert.NotEmpty(matches[0].RuntimeConditionalSkipReasons);
            Assert.All(
                matches[0].RuntimeConditionalSkipReasons,
                static reason => Assert.StartsWith("Live raw Lean report is ", reason, StringComparison.Ordinal));
            Assert.NotEmpty(matches[0].RuntimeConditionalSkipContracts);
            Assert.All(matches[0].RuntimeConditionalSkipContracts, static contract => Assert.Equal(64, contract.Length));
        }

        Assert.All(
            map.Methods.Where(static method => method.Id.StartsWith(
                "RetiredLedgerSurfaceTests.",
                StringComparison.Ordinal)),
            static method => Assert.True(method.IsUnknown));

        var self = Assert.Single(map.Methods, static method => method.Id ==
            "ScribeTestMapSymbolBindingTests.RepositoryMapIncludesDerivedFactsAndRetiredLedgerFixtureClosure");
        Assert.Contains("Blueprint", self.Paths);
        Assert.Contains("tools", self.Paths);
        Assert.False(self.IsUnknown, string.Join(',', self.UnknownReasons));
    }

    private static ScribeTestMap Derive(string source) =>
        ScribeTestMapDeriverTests.DeriveSources([new("SymbolBindingTests.cs", source)]);

    private static ScribeTestMap DeriveDeclaredRepositoryMap()
    {
        var root = RepositoryLayout.FindRoot();
        var tracked = GitIndexRepositoryFiles
            .EnumerateDeclared(root, "Blueprint")
            .Concat(GitIndexRepositoryFiles.EnumerateDeclared(root, "tools"))
            .Where(static file => file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                || file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal)
                || file.RelativePath.EndsWith("packages.lock.json", StringComparison.Ordinal))
            .Select(static file => new ScribeTrackedSource(
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();
        var projects = tracked
            .Where(static file => file.Path.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(static file => file.Path);
        return ScribeTestMapDeriver.DeriveTracked(
            tracked,
            QueryCompileMap(root, projects));
    }

    private static MsBuildCompileMap QueryCompileMap(string root, IEnumerable<string> projects) =>
        MsBuildCompileOracle.Query(root, projects);

    private static RepositorySnapshot MetadataSnapshot(
        string projectPath,
        string? packageLock,
        string source)
    {
        var directory = projectPath[..projectPath.LastIndexOf('/')];
        var files = new List<(string Path, string Content)>
        {
            (projectPath, """
                <Project Sdk="Microsoft.NET.Sdk">
                  <PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>
                  <ItemGroup><PackageReference Include="xunit" Version="2.9.3" /></ItemGroup>
                </Project>
                """),
            ($"{directory}/MetadataTests.cs", source),
            ("tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\" />"),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\" />"),
        };
        if (packageLock is not null) files.Add(($"{directory}/packages.lock.json", packageLock));
        return ScribeTestMapDeriverTests.Snapshot(files.ToArray());
    }

    private const string MissingXunitLock = """
        {
          "version": 1,
          "dependencies": {
            "net10.0": {
              "xunit": { "type": "Direct", "resolved": "999.0.0-metadata-unavailable" },
              "xunit.assert": { "type": "Transitive", "resolved": "999.0.0-metadata-unavailable" },
              "xunit.core": { "type": "Transitive", "resolved": "999.0.0-metadata-unavailable" },
              "xunit.extensibility.core": { "type": "Transitive", "resolved": "999.0.0-metadata-unavailable" }
            }
          }
        }
        """;

    private const string IncompleteXunitLock = """
        {
          "version": 1,
          "dependencies": {
            "net10.0": {
              "xunit": { "type": "Direct", "resolved": "999.0.0-metadata-unavailable" },
              "xunit.assert": { "type": "Transitive", "resolved": "999.0.0-metadata-unavailable" }
            }
          }
        }
        """;
}
