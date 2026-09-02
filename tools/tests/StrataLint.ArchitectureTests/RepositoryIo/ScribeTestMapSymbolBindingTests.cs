namespace StrataLint.ArchitectureTests;

public sealed class ScribeTestMapSymbolBindingTests
{
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

        Assert.Equal(2, tests.Length);
        Assert.All(tests, static method => Assert.True(method.IsUnknown));
        Assert.All(tests, static method =>
            Assert.Contains(TestMapUnknownReason.MetadataUnavailable, method.UnknownReasons));

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
        Assert.All(
            map.Methods.Where(static method => method.Id.StartsWith(
                "RetiredLedgerSurfaceTests.",
                StringComparison.Ordinal)),
            static method => Assert.True(method.IsUnknown));

        var self = Assert.Single(map.Methods, static method => method.Id ==
            "ScribeTestMapSymbolBindingTests.RepositoryMapIncludesDerivedFactsAndRetiredLedgerFixtureClosure");
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
