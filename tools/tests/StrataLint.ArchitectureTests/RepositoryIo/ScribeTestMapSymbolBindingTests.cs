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
                public LiveReportFactAttribute() => File.ReadAllText(
                  Path.Combine(RepositoryLayout.FindRoot(), "D5", "attribute.lean"));
              }
            }
            """;

        var method = Assert.Single(Derive(source).Methods);

        Assert.Equal("DerivedFactTests.Reads", method.Id);
        Assert.Equal(["D5/attribute.lean"], method.Paths);
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
            ("tools/tests/Shared.Tests/SharedReader.cs", """
                using System.IO;
                namespace Shared;
                internal static class RepositoryLayout {
                  internal static string FindRoot() => string.Empty;
                }
                public static class SharedReader {
                  public static void Read() => File.ReadAllText(
                    Path.Combine(RepositoryLayout.FindRoot(), "D5", "shared.lean"));
                }
                """),
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
        var map = ScribeTestMapDeriver.DeriveRepository(RepositoryLayout.FindRoot());
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
        }

        Assert.All(
            map.Methods.Where(static method => method.Id.StartsWith(
                "RetiredLedgerSurfaceTests.",
                StringComparison.Ordinal)),
            static method => Assert.True(method.IsUnknown));
    }

    private static ScribeTestMap Derive(string source) =>
        ScribeTestMapDeriverTests.DeriveSources([new("SymbolBindingTests.cs", source)]);
}
