using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class TomlGoldenLoaderTests
{
    [Fact]
    public void CanonicalFixtureLoads()
    {
        var source = TomlGoldenLoader.LoadFile(Fixture("valid.toml"));

        var testCase = Assert.Single(source.Cases);
        Assert.Equal("valid", testCase.Name);
        Assert.Empty(testCase.BaselineMutations);
        Assert.Empty(testCase.Mutations);
        Assert.Empty(testCase.ExpectedDiagnostics);
    }

    [Theory]
    [InlineData("unknown-key.toml", "unknown key 'unexpected'")]
    [InlineData("unknown-op.toml", "unknown golden mutation op 'explode'")]
    [InlineData("unknown-stratum.toml", "key 'stratum' has unknown stratum 'S5'")]
    [InlineData("wrong-type.toml", "key 'count' must be an integer")]
    public void InvalidFixtureFailsClosed(string fileName, string expectedMessage)
    {
        var exception = Assert.Throws<FormatException>(
            () => TomlGoldenLoader.LoadFile(Fixture(fileName)));

        Assert.Contains(expectedMessage, exception.Message, StringComparison.Ordinal);
    }

    private static string Fixture(string name) => Path.Combine(
        FindRepositoryRoot(),
        "Meta",
        "StrataLint",
        "StrataLint.Tests",
        "Golden",
        "Fixtures",
        name);

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
