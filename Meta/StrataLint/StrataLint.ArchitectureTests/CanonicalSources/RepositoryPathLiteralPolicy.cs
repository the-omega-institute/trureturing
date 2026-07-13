using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal sealed record RepositoryPathLiteralFinding(string Path, string Value, string Message);

internal static class RepositoryPathLiteralPolicy
{
    internal static IReadOnlyList<RepositoryPathLiteralFinding> InspectRepository(string repositoryRoot)
    {
        var existingFiles = CSharpRepositorySources.ExistingFiles(repositoryRoot);
        return CSharpRepositorySources.Enumerate(repositoryRoot)
            .SelectMany(source => InspectSource(
                source.RelativePath,
                File.ReadAllText(source.FullPath),
                existingFiles))
            .ToArray();
    }

    internal static IReadOnlyList<RepositoryPathLiteralFinding> InspectSource(
        string path,
        string source,
        IReadOnlySet<string> existingRepositoryFiles)
    {
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        return root.DescendantNodes()
            .OfType<LiteralExpressionSyntax>()
            .Where(static literal => literal.IsKind(SyntaxKind.StringLiteralExpression))
            .Where(literal => IsForbidden(literal, existingRepositoryFiles))
            .Select(literal => new RepositoryPathLiteralFinding(
                path,
                literal.Token.ValueText,
                $"C# string literal points to existing repository file {literal.Token.ValueText}; define it once as const string and reference that constant"))
            .ToArray();
    }

    private static bool IsForbidden(
        LiteralExpressionSyntax literal,
        IReadOnlySet<string> existingRepositoryFiles)
    {
        var value = literal.Token.ValueText;
        return value.Count(static character => character == '/') >= 2
            && existingRepositoryFiles.Contains(value)
            && !IsConstDefinition(literal);
    }

    private static bool IsConstDefinition(LiteralExpressionSyntax literal)
    {
        var variable = literal.Parent is EqualsValueClauseSyntax { Parent: VariableDeclaratorSyntax declarator }
            ? declarator
            : null;
        if (variable?.Initializer?.Value != literal
            || variable.Parent is not VariableDeclarationSyntax declaration)
        {
            return false;
        }

        return declaration.Parent switch
        {
            FieldDeclarationSyntax field => field.Modifiers.Any(static modifier =>
                modifier.IsKind(SyntaxKind.ConstKeyword)),
            LocalDeclarationStatementSyntax local => local.Modifiers.Any(static modifier =>
                modifier.IsKind(SyntaxKind.ConstKeyword)),
            _ => false,
        };
    }
}
