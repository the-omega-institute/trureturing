using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal sealed record GoldenCorpusStorageFinding(string Path, string Message);

internal static class GoldenCorpusStoragePolicy
{
    internal static IReadOnlyList<GoldenCorpusStorageFinding> InspectRepository(
        string repositoryRoot)
    {
        var findings = new List<GoldenCorpusStorageFinding>();
        foreach (var (relativePath, path) in CSharpRepositorySources.Enumerate(repositoryRoot))
        {
            findings.AddRange(InspectSource(relativePath, File.ReadAllText(path)));
        }

        return findings;
    }

    internal static IReadOnlyList<GoldenCorpusStorageFinding> InspectSource(
        string path,
        string source)
    {
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        var findings = new List<GoldenCorpusStorageFinding>();
        foreach (var creation in root.DescendantNodes().OfType<ObjectCreationExpressionSyntax>())
        {
            if (RightmostIdentifier(creation.Type) != "GoldenCase"
                || creation.ArgumentList?.Arguments.FirstOrDefault()?.Expression
                    is not LiteralExpressionSyntax literal
                || !literal.IsKind(SyntaxKind.StringLiteralExpression))
            {
                continue;
            }

            findings.Add(Finding(path));
        }

        foreach (var invocation in root.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            if (invocation.Expression is not IdentifierNameSyntax { Identifier.ValueText: "C" }
                || invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression
                    is not LiteralExpressionSyntax literal
                || !literal.IsKind(SyntaxKind.StringLiteralExpression)
                || invocation.Ancestors().OfType<TypeDeclarationSyntax>().FirstOrDefault()
                    is not { Identifier.ValueText: "GoldenCorpus" })
            {
                continue;
            }

            findings.Add(Finding(path));
        }

        return findings;
    }

    private static GoldenCorpusStorageFinding Finding(string path) => new(
        path,
        "C# golden case data is forbidden; declare cases under Meta/StrataLint/Golden/cases");

    private static string RightmostIdentifier(TypeSyntax type) => type switch
    {
        IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
        QualifiedNameSyntax qualified => qualified.Right.Identifier.ValueText,
        AliasQualifiedNameSyntax alias => alias.Name.Identifier.ValueText,
        _ => string.Empty,
    };
}
