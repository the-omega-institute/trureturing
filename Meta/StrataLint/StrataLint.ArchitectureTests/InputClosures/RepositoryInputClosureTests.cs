namespace StrataLint.ArchitectureTests;

public sealed class RepositoryInputClosureTests
{
    [Fact]
    public void EveryFactAndTheoryHasANonEmptyDerivedEffect()
    {
        var root = RepositoryLayout.FindRoot();
        var result = RepositoryInputClosureDeriver.DeriveRepositoryTests(root);

        Assert.NotEmpty(result);
        var missing = result.Where(static effect => effect.Patterns.Count == 0).ToArray();
        Assert.True(missing.Length == 0, RepositoryInputClosureReadout.Render(result));
    }

    [Fact]
    public void EveryRepositoryReadDeclarationHasAParseableKindAndPath()
    {
        var result = RepositoryInputClosureDeriver.DeriveRepositoryTests(RepositoryLayout.FindRoot());

        Assert.True(result.DeclarationFindings.Count == 0, RepositoryInputClosureReadout.Render(result));
    }

    [Fact]
    public void DerivedInputClosureAggregatesAreNotTracked()
    {
        var root = RepositoryLayout.FindRoot();
        var directory = Path.Combine(root,
            "Meta/StrataLint/StrataLint.ArchitectureTests/InputClosures/Derived");

        Assert.False(Directory.Exists(directory), $"derived aggregate must not be stored at {directory}");
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
    public void ExternalAssemblyCallEdgeFailsClosedToAll()
    {
        const string source = """
            using System;
            using Xunit;
            public static class ExternalEdgeCase
            {
                [Fact]
                public static void Test() => Console.WriteLine("external");
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
    public void ViolationReadoutNamesTestDerivedEffectAndAllReason()
    {
        const string source = """
            using Xunit;
            public static class DiagnosticCase
            {
                [Fact]
                public static void Test() => MissingAssembly.Loader.Read();
            }
            """;

        var readout = RepositoryInputClosureReadout.Render(
            RepositoryInputClosureDeriver.DeriveSynthetic(source));

        Assert.Contains("DiagnosticCase.Test", readout, StringComparison.Ordinal);
        Assert.Contains("\tAll\tfail-closed:", readout, StringComparison.Ordinal);
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
