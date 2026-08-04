using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class GoldenCorpusMaterializerTests
{
    private const string ValidGoldenFixturePath =
        "Meta/StrataLint/StrataLint.Tests/Golden/Fixtures/valid.toml";
    private const string AnchorCatalogPath =
        "Meta/StrataLint/Generated/anchor-catalog.v1.json";
    private const string SpecificationPath = "docs/develop/spec/golden-ledger-repo-spec.md";

    [Fact]
    public void MaterializerLoadsEveryCaseFromTheBaseTomlCorpusWithoutExpectedLabels()
    {
        var root = FindRepositoryRoot();
        var source = TomlGoldenLoader.LoadRepository(root);

        var corpus = GoldenCorpusMaterializer.Materialize(root);
        var canonical = Encoding.UTF8.GetString(corpus.CanonicalBytes.AsSpan());

        Assert.Equal(source.Cases.Count, corpus.CaseIds.Length);
        Assert.Equal(
            source.Cases.Select(static item => $"golden:{item.Name}").Order(StringComparer.Ordinal),
            corpus.CaseIds);
        Assert.DoesNotContain("expected", canonical, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void MaterializedCorpusRootAndBytesAreStable()
    {
        var root = FindRepositoryRoot();

        var first = GoldenCorpusMaterializer.Materialize(root);
        var second = GoldenCorpusMaterializer.Materialize(root);

        Assert.Equal(first.Root, second.Root);
        Assert.True(first.CanonicalBytes.AsSpan().SequenceEqual(second.CanonicalBytes.AsSpan()));
    }

    [Fact]
    public void PopulateDirectoryUsesNonProjectionCapacityWitnesses()
    {
        var corpus = GoldenCorpusMaterializer.Materialize(FindRepositoryRoot());
        var canonical = Encoding.UTF8.GetString(corpus.CanonicalBytes.AsSpan());

        for (var index = 0; index < 13; index++)
        {
            Assert.Contains(
                $"Golden/cases/CapacityExtra{index:00}.toml",
                canonical,
                StringComparison.Ordinal);
            Assert.DoesNotContain(
                $"Blueprint/D5/S0/Carrier/Extra{index:00}.md",
                canonical,
                StringComparison.Ordinal);
        }
    }

    [Fact]
    public void MaterializerFailsClosedWhenTheExternalFixtureRegistryIsAbsent()
    {
        var repositoryRoot = FindRepositoryRoot();
        using var temporary = new TemporaryDirectory();
        Copy(
            repositoryRoot,
            temporary.Path,
            ValidGoldenFixturePath,
            "Golden/cases/valid.toml");
        Copy(
            repositoryRoot,
            temporary.Path,
            AnchorCatalogPath);
        Copy(
            repositoryRoot,
            temporary.Path,
            SpecificationPath);

        var exception = Assert.Throws<FileNotFoundException>(
            () => GoldenCorpusMaterializer.Materialize(temporary.Path));

        Assert.Contains("Golden/fixture-registry.yaml", exception.Message, StringComparison.Ordinal);
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }

    private static void Copy(
        string sourceRoot,
        string destinationRoot,
        string sourceRelativePath,
        string? destinationRelativePath = null)
    {
        var relativePath = destinationRelativePath ?? sourceRelativePath;
        var destination = Path.Combine(destinationRoot, relativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
        File.Copy(Path.Combine(sourceRoot, sourceRelativePath), destination);
    }

    private sealed class TemporaryDirectory : IDisposable
    {
        internal TemporaryDirectory() => Path = Directory.CreateTempSubdirectory(
            "stratalint-golden-fixture-").FullName;

        internal string Path { get; }

        public void Dispose() => Directory.Delete(Path, recursive: true);
    }
}
