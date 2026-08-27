using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class BoundedProcessRunnerBudgetTests
{
    [Fact]
    public void TrackedTestDurationsHaveOneAnnotatedSource()
    {
        const string budgetPath = "tools/tests/StrataLint.Tests/TestBudgets.cs";
        var sources = GitIndexRepositoryFiles.Enumerate(RepositoryLayout.FindRoot())
            .Where(file => file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                && !file.RelativePath.StartsWith("tools/tests/BannedApiCompileFailProof/", StringComparison.Ordinal)
                && file.RelativePath != budgetPath)
            .Select(file => (file.RelativePath, Content: string.Join('\n', File.ReadLines(file.FullPath))))
            .ToArray();

        Assert.Empty(FindTimeSpanFactorySites(sources));
    }

    [Fact]
    public void EveryPublishedTestBudgetHasOneSourceClassification()
    {
        const string budgetPath = "tools/tests/StrataLint.Tests/TestBudgets.cs";
        var tree = CSharpSyntaxTree.ParseText(
            TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                "tools/tests/StrataLint.Tests/TestBudgets.cs")),
            new CSharpParseOptions(LanguageVersion.Latest),
            budgetPath);
        var declarations = tree.GetRoot().DescendantNodes()
            .OfType<FieldDeclarationSyntax>()
            .Where(static field => field.Declaration.Type.ToString() == nameof(TimeSpan))
            .ToArray();
        var expectedNames = typeof(TestBudgets)
            .GetFields(BindingFlags.Public | BindingFlags.Static)
            .Where(static field => field.FieldType == typeof(TimeSpan))
            .Select(static field => field.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var actualNames = declarations
            .SelectMany(static field => field.Declaration.Variables)
            .Select(static variable => variable.Identifier.ValueText)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(expectedNames, actualNames);
        Assert.All(declarations, declaration =>
        {
            Assert.Single(declaration.Declaration.Variables);
            var text = declaration.ToFullString();
            var classifications = new[] { "pinned-production-constant", "infrastructure-hang-guard" }
                .Count(marker => text.Contains(marker, StringComparison.Ordinal));
            Assert.True(
                classifications == 1,
                $"{budgetPath}:{declaration.GetLocation().GetLineSpan().StartLinePosition.Line + 1} "
                    + "must have exactly one source classification");
        });
    }

    [Fact]
    public void DurationAliasCannotBypassTrackedDurationSource()
    {
        var sites = FindTimeSpanFactorySites(
        [
            (
                "tools/tests/Synthetic/AliasDuration.cs",
                "using Duration = System.TimeSpan; class AliasDuration { object Value() => Duration.FromSeconds(1); }")
        ]);

        Assert.Equal(["tools/tests/Synthetic/AliasDuration.cs:1"], sites);
    }

    [Fact]
    public void ImplicitSystemUsingAndTargetTypedConstructorCannotBypassTrackedDurationSource()
    {
        var sites = FindTimeSpanFactorySites(
        [
            (
                "tools/tests/Synthetic/ImplicitDuration.cs",
                "class ImplicitDuration { TimeSpan Value() => new(1); }")
        ]);

        Assert.Equal(["tools/tests/Synthetic/ImplicitDuration.cs:1"], sites);
    }

    [Fact]
    public void TestScratchWallClockBridgeHasOneExactLocationPerCapability()
    {
        const string bridgePath = "tools/tests/StrataLint.Tests/TestScratchRoot.cs";
        var repositoryRoot = RepositoryLayout.FindRoot();
        var systemUtcNow = string.Concat("TimeProvider.System", ".GetUtcNow()");
        var retryWait = string.Concat("retryPause", ".Wait(25)");
        var sources = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .Select(file => (
                file.RelativePath,
                Content: string.Join('\n', File.ReadLines(file.FullPath))))
            .ToArray();
        var utcNow = sources
            .SelectMany(source => Enumerable.Repeat(
                source.RelativePath,
                CountOccurrences(source.Content, systemUtcNow)))
            .ToArray();
        var retryPause = sources
            .SelectMany(source => Enumerable.Repeat(
                source.RelativePath,
                CountOccurrences(source.Content, retryWait)))
            .ToArray();
        var bridge = Assert.Single(sources, static source => source.RelativePath == bridgePath).Content;

        Assert.Equal([bridgePath], utcNow);
        Assert.Equal([bridgePath], retryPause);
        Assert.Contains("internal static class TestEnvironmentBridge", bridge, StringComparison.Ordinal);
        Assert.Contains("internal static DateTime UtcNow()", bridge, StringComparison.Ordinal);
        Assert.Contains("internal static void PauseBeforeCleanupRetry()", bridge, StringComparison.Ordinal);
    }

    private static int CountOccurrences(string content, string value)
    {
        var count = 0;
        var index = 0;
        while ((index = content.IndexOf(value, index, StringComparison.Ordinal)) >= 0)
        {
            count++;
            index += value.Length;
        }

        return count;
    }

    private static IReadOnlyList<string> FindTimeSpanFactorySites(
        IReadOnlyList<(string RelativePath, string Content)> sources)
    {
        var trees = sources
            .Select(source => CSharpSyntaxTree.ParseText(
                source.Content,
                new CSharpParseOptions(LanguageVersion.Latest),
                source.RelativePath))
            .ToArray();
        var implicitUsings = CSharpSyntaxTree.ParseText(
            "global using System;",
            new CSharpParseOptions(LanguageVersion.Latest),
            "tools/tests/Synthetic/ImplicitUsings.g.cs");
        var compilation = CSharpCompilation.Create(
            "TrackedTestDurationProbe",
            trees.Prepend(implicitUsings),
            [MetadataReference.CreateFromFile(typeof(TimeSpan).Assembly.Location)],
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
        var timeSpanType = compilation.GetTypeByMetadataName("System.TimeSpan")
            ?? throw new InvalidOperationException("System.TimeSpan is absent from the semantic compilation");

        return trees
            .SelectMany(tree =>
            {
                var model = compilation.GetSemanticModel(tree);
                return tree.GetRoot().DescendantNodes()
                    .Where(node =>
                    {
                        var symbol = model.GetSymbolInfo(node).Symbol;
                        return node switch
                        {
                            InvocationExpressionSyntax => symbol is IMethodSymbol method
                                && SymbolEqualityComparer.Default.Equals(method.ContainingType, timeSpanType)
                                && SymbolEqualityComparer.Default.Equals(method.ReturnType, timeSpanType),
                            ObjectCreationExpressionSyntax or ImplicitObjectCreationExpressionSyntax =>
                                symbol is IMethodSymbol constructor
                                && SymbolEqualityComparer.Default.Equals(constructor.ContainingType, timeSpanType),
                            SimpleNameSyntax => symbol switch
                            {
                                IFieldSymbol field => field.IsStatic
                                    && SymbolEqualityComparer.Default.Equals(field.ContainingType, timeSpanType)
                                    && SymbolEqualityComparer.Default.Equals(field.Type, timeSpanType),
                                IPropertySymbol property => property.IsStatic
                                    && SymbolEqualityComparer.Default.Equals(property.ContainingType, timeSpanType)
                                    && SymbolEqualityComparer.Default.Equals(property.Type, timeSpanType),
                                _ => false,
                            },
                            _ => false,
                        };
                    })
                    .Select(node =>
                    {
                        var line = node.GetLocation().GetLineSpan().StartLinePosition.Line + 1;
                        return $"{tree.FilePath}:{line}";
                    })
                    .Distinct(StringComparer.Ordinal);
            })
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    [Fact]
    public void HangDetectionBudgetIsFiniteAndPositive()
    {
        var field = typeof(BoundedProcessRunner).GetField(
            "HangDetectionBudget",
            BindingFlags.NonPublic | BindingFlags.Static);

        Assert.NotNull(field);
        var budget = Assert.IsType<TimeSpan>(field.GetValue(null));
        Assert.True(budget > TestBudgets.ZeroDuration);
        Assert.NotEqual(Timeout.InfiniteTimeSpan, budget);
    }

}
