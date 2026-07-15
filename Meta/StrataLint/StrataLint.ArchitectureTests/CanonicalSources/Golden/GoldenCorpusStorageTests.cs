using System.Collections;
using System.Reflection;
using StrataLint.Cli;

namespace StrataLint.ArchitectureTests;

public sealed class GoldenCorpusStorageTests
{
    [Fact]
    public void RepositoryCSharpContainsNoGoldenCaseDeclarations()
    {
        Assert.Empty(GoldenCorpusStoragePolicy.InspectRepository(RepositoryLayout.FindRoot()));
    }

    [Theory]
    [InlineData("var item = new GoldenCase(\"synthetic\", [], [], [], []);")]
    [InlineData("internal static partial class GoldenCorpus { private static object X => C(\"synthetic\", [], [], []); }")]
    public void CSharpGoldenCaseDeclarationIsRejectedByTheRedFixture(string source)
    {
        var finding = Assert.Single(GoldenCorpusStoragePolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source));

        Assert.Contains("Meta/StrataLint/Golden/cases", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SchemaDeclarationIsNotMistakenForCaseData()
    {
        const string source =
            "internal sealed record GoldenCase(string Name, IReadOnlyList<object> Mutations);";

        Assert.Empty(GoldenCorpusStoragePolicy.InspectSource(
            "Meta/StrataLint/SyntheticSchema.cs",
            source));
    }

    [Fact]
    public void CanonicalTomlDirectoryIsTheOnlyCaseAuthority()
    {
        var root = RepositoryLayout.FindRoot();
        var directory = Path.Combine(root, "Meta", "StrataLint", "Golden", "cases");
        Assert.Equal(4, Directory.EnumerateFiles(directory, "*.toml").Count());
        var loader = typeof(StrataLint.Cli.Program).Assembly.GetType(
            "StrataLint.Cli.TomlGoldenLoader",
            throwOnError: true)!;
        var corpus = loader.GetMethod(
            "LoadRepository",
            BindingFlags.Static | BindingFlags.NonPublic)!.Invoke(null, [root])!;
        var cases = (IEnumerable)corpus.GetType().GetProperty(
            "Cases",
            BindingFlags.Instance | BindingFlags.NonPublic)!.GetValue(corpus)!;
        Assert.Equal(111, cases.Cast<object>().Count());
        Assert.Empty(Directory.EnumerateFiles(
            Path.Combine(root, "Meta", "StrataLint", "StrataLint.Cli", "Golden"),
            "GoldenCorpus.Cases*.cs"));
    }
}
