namespace StrataLint.ArchitectureTests;

public sealed class RepositoryInputClosureTests
{
    [Fact]
    public void EveryTestHasANonEmptyParseableDerivedEffectAndArtifactIsCurrent()
    {
        var root = RepositoryLayout.FindRoot();
        var result = RepositoryInputClosureDeriver.DeriveRepositoryTests(root);

        Assert.NotEmpty(result);
        Assert.All(result, effect => Assert.NotEmpty(effect.Patterns));
        Assert.Empty(result.DeclarationFindings);

        var rendered = RepositoryInputClosureArtifact.Render(result);
        if (Environment.GetEnvironmentVariable("STRATALINT_UPDATE_INPUT_CLOSURES") == "1")
        {
            RepositoryInputClosureArtifact.Write(root, rendered);
        }

        var directory = Path.Combine(root, RepositoryInputClosureArtifact.RelativeDirectory);
        var actualNames = Directory.Exists(directory)
            ? Directory.EnumerateFiles(directory, "*.tsv").Select(Path.GetFileName).Order().ToArray()
            : [];
        Assert.Equal(rendered.Keys.Order().ToArray(), actualNames);
        foreach (var (name, expected) in rendered)
        {
            Assert.Equal(expected, File.ReadAllText(Path.Combine(directory, name)));
        }
    }

    [Fact]
    public void UnknownCallEdgeFailsClosedToAll()
    {
        const string source = """
            using Xunit;
            public static class UnknownEdgeCase
            {
                [Fact]
                public static void Test() => MissingAssembly.Loader.Read();
            }
            """;

        var result = RepositoryInputClosureDeriver.DeriveSynthetic(source);

        Assert.Equal(["All"], result.Single().Patterns);
    }

    [Fact]
    public void DynamicPathCannotClaimAnExactEffect()
    {
        const string source = """
            using System.IO;
            using StrataLint.Engine;
            using Xunit;
            public static class DynamicExactCase
            {
                [RepositoryReadPattern(RepositoryReadPatternKind.Exact, "Meta/FILEMAP.toml")]
                private static void Read(string root, string name) =>
                    File.ReadAllText(Path.Combine(root, name));

                [Fact]
                public static void Test() => Read(".", "Meta/FILEMAP.toml");
            }
            """;

        var result = RepositoryInputClosureDeriver.DeriveSynthetic(source);

        Assert.Equal(["All"], result.Single().Patterns);
        Assert.Contains(result.DeclarationFindings, finding =>
            finding.Contains("cannot prove Exact", StringComparison.Ordinal));
    }

    [Fact]
    public void ConstantPathCanDeclareAnExactEffect()
    {
        const string source = """
            using System.IO;
            using StrataLint.Engine;
            using Xunit;
            public static class StaticExactCase
            {
                private const string PathName = "Meta/FILEMAP.toml";

                [RepositoryReadPattern(RepositoryReadPatternKind.Exact, PathName)]
                private static void Read(string root) =>
                    File.ReadAllText(Path.Combine(root, PathName));

                [Fact]
                public static void Test() => Read(".");
            }
            """;

        var result = RepositoryInputClosureDeriver.DeriveSynthetic(source);

        Assert.Equal(["Exact(Meta/FILEMAP.toml)"], result.Single().Patterns);
        Assert.Empty(result.DeclarationFindings);
    }

    [Fact]
    public void RuleFixtureKeepsConditionalRepositoryReadsAtMethodBoundaries()
    {
        var result = RepositoryInputClosureDeriver.DeriveRepository(RepositoryLayout.FindRoot());

        Assert.Equal(
            [
                "Exact(Meta/Digestion/atomizers.toml)",
                "Exact(Meta/StrataLint/Generated/anchor-catalog.v1.json)",
            ],
            result.EffectFor("StrataLint.Tests.RuleFixture..ctor").Patterns);
        Assert.Equal(
            ["Exact(Evidence/D5/values.json)"],
            result.EffectFor("StrataLint.Tests.RuleFixture.AddValuesProjection").Patterns);
    }
}
