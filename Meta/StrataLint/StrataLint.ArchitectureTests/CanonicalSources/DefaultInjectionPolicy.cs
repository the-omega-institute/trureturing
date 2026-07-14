using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

internal sealed record DefaultInjectionFinding(string Path, string Message);

internal static class DefaultInjectionPolicy
{
    internal static IReadOnlyList<DefaultInjectionFinding> InspectRepository(string repositoryRoot) =>
        CSharpRepositorySources.Enumerate(repositoryRoot)
            .SelectMany(source => InspectSource(
                source.RelativePath,
                File.ReadAllText(source.FullPath)))
            .ToArray();

    internal static IReadOnlyList<DefaultInjectionFinding> InspectSource(string path, string source)
    {
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        var findings = new List<DefaultInjectionFinding>();
        foreach (var parameter in root.DescendantNodes().OfType<ParameterSyntax>())
        {
            if (parameter.Default?.Value is not LiteralExpressionSyntax literal
                || !literal.IsKind(SyntaxKind.StringLiteralExpression)
                || !IsPublicDslOrBuilderParameter(parameter)
                || !IsCanonicalValue(literal.Token.ValueText))
            {
                continue;
            }

            findings.Add(new DefaultInjectionFinding(
                path,
                $"public DSL/builder parameter {parameter.Identifier.ValueText} injects canonical value {literal.Token.ValueText} as a default"));
        }

        return findings;
    }

    private static bool IsPublicDslOrBuilderParameter(ParameterSyntax parameter)
    {
        var type = parameter.Ancestors().OfType<TypeDeclarationSyntax>().FirstOrDefault();
        if (type is null
            || !IsEffectivelyPublic(type)
            || !(type.Identifier.ValueText.EndsWith("Dsl", StringComparison.Ordinal)
                || type.Identifier.ValueText.EndsWith("Builder", StringComparison.Ordinal)))
        {
            return false;
        }

        if (parameter.Parent?.Parent == type)
        {
            return true;
        }

        var member = parameter.Ancestors().OfType<MemberDeclarationSyntax>().FirstOrDefault();
        return member switch
        {
            MethodDeclarationSyntax method =>
                type is InterfaceDeclarationSyntax
                || method.Modifiers.Any(SyntaxKind.PublicKeyword),
            ConstructorDeclarationSyntax constructor =>
                constructor.Modifiers.Any(SyntaxKind.PublicKeyword),
            _ => false,
        };
    }

    private static bool IsEffectivelyPublic(TypeDeclarationSyntax type) =>
        type.Modifiers.Any(SyntaxKind.PublicKeyword)
        && type.Ancestors()
            .OfType<TypeDeclarationSyntax>()
            .All(static outer => outer.Modifiers.Any(SyntaxKind.PublicKeyword));

    private static bool IsCanonicalValue(string value) =>
        Gid.TryParse(value, out _)
        || CaseId.TryCreate(value, out _)
        || Anchor.TryParseCanonical(value) is AnchorParseResult.Parsed;
}
