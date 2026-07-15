using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class GoldenRecordCommandTests
{
    private static readonly string[] RequiredFixturePaths =
    [
        RuleFixture.AnchorCatalogPath,
        RuleFixture.SpecificationPath,
    ];

    [Fact]
    public void RecordRewritesOnlyExpectedDiagnosticsAndIsByteStable()
    {
        using var temporary = new TemporaryDirectory();
        CopyGoldenFixture(temporary.Path);
        var casePath = Path.Combine(
            temporary.Path,
            TomlGoldenLoader.RelativeDirectory,
            "structure-and-identities.toml");
        var text = File.ReadAllText(casePath, Encoding.UTF8);
        const string expected = "expected_diagnostics = []";
        var index = text.IndexOf(expected, StringComparison.Ordinal);
        Assert.True(index >= 0);
        const string wrong =
            "expected_diagnostics = [{ rule = 1, path = \"D5/S0/Carrier/Ring.lean\", message = \"wrong snapshot\" }]";
        File.WriteAllText(
            casePath,
            string.Concat(text.AsSpan(0, index), wrong, text.AsSpan(index + expected.Length)),
            new UTF8Encoding(false));
        var before = TomlGoldenLoader.LoadRepository(temporary.Path);
        var behaviorBefore = WithoutExpectations(before);

        var first = GoldenRecordCommand.Run(temporary.Path, []);

        Assert.True(first.Success, first.Error);
        Assert.Contains("cases=111", first.Output, StringComparison.Ordinal);
        Assert.Contains("changed_files=1", first.Output, StringComparison.Ordinal);
        var after = TomlGoldenLoader.LoadRepository(temporary.Path);
        Assert.Equal(behaviorBefore, WithoutExpectations(after));
        Assert.Empty(after.Cases.Single(static item => item.Name == "valid-minimal-unit").ExpectedDiagnostics);
        var firstBytes = after.Files.ToDictionary(
            static file => file.Path,
            static file => File.ReadAllBytes(file.Path),
            StringComparer.Ordinal);

        var second = GoldenRecordCommand.Run(temporary.Path, []);

        Assert.True(second.Success, second.Error);
        Assert.Contains("changed_files=0", second.Output, StringComparison.Ordinal);
        Assert.All(firstBytes, item => Assert.Equal(item.Value, File.ReadAllBytes(item.Key)));
    }

    private static byte[][] WithoutExpectations(GoldenCorpusSet corpus) => corpus.Files
        .Select(static file => TomlGoldenWriter.Write(file.Cases
            .Select(static item => item with
            {
                ExpectedDiagnostics = Array.Empty<GoldenDiagnostic>(),
            })
            .ToArray()))
        .ToArray();

    private static void CopyGoldenFixture(string targetRoot)
    {
        var sourceRoot = FindRepositoryRoot();
        foreach (var path in RequiredFixturePaths)
        {
            Copy(sourceRoot, targetRoot, path);
        }

        var sourceCases = Path.Combine(sourceRoot, TomlGoldenLoader.RelativeDirectory);
        foreach (var path in Directory.EnumerateFiles(sourceCases, "*.toml"))
        {
            Copy(
                sourceRoot,
                targetRoot,
                Path.GetRelativePath(sourceRoot, path).Replace(Path.DirectorySeparatorChar, '/'));
        }
    }

    private static void Copy(string sourceRoot, string targetRoot, string relativePath)
    {
        var source = Path.Combine(sourceRoot, relativePath);
        var target = Path.Combine(targetRoot, relativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
        File.Copy(source, target);
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
}
