using System.Collections.Immutable;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.Engine;

internal enum ScribeLegacyConstructor
{
    DescribeTheorem,
    DescribeDefinition,
    DescribeProposition,
    DescribeLemma,
    LeanTheorem,
    LeanDeclarationRefCreate,
    Header,
    UnassessedProvenance,
}

internal static class ScribeLegacyConstructorScanner
{
    internal static ImmutableDictionary<ScribeLegacyConstructor, int> Count(string source)
    {
        ArgumentNullException.ThrowIfNull(source);
        var root = CSharpSyntaxTree.ParseText(source).GetCompilationUnitRoot();
        var builder = Enum.GetValues<ScribeLegacyConstructor>()
            .ToImmutableDictionary(static kind => kind, static _ => 0)
            .ToBuilder();
        var importsDefinitionDsl = root.Usings.Any(static item =>
            item.StaticKeyword.RawKind != 0 && RightmostIdentifier(item.Name) == "DefinitionDsl");

        foreach (var invocation in root.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            var kind = Classify(invocation.Expression, importsDefinitionDsl);
            if (kind is not null) builder[kind.Value]++;
        }

        return builder.ToImmutable();
    }

    private static ScribeLegacyConstructor? Classify(ExpressionSyntax expression, bool importsDefinitionDsl) =>
        expression switch
        {
            _ when IsPath(expression, "DocumentBlock", "Describe", "Theorem") => ScribeLegacyConstructor.DescribeTheorem,
            _ when IsPath(expression, "DocumentBlock", "Describe", "Definition") => ScribeLegacyConstructor.DescribeDefinition,
            _ when IsPath(expression, "DocumentBlock", "Describe", "Proposition") => ScribeLegacyConstructor.DescribeProposition,
            _ when IsPath(expression, "DocumentBlock", "Describe", "Lemma") => ScribeLegacyConstructor.DescribeLemma,
            _ when IsPath(expression, "DefinitionDsl", "LeanTheorem") => ScribeLegacyConstructor.LeanTheorem,
            _ when IsPath(expression, "LeanDeclarationRef", "Create") => ScribeLegacyConstructor.LeanDeclarationRefCreate,
            _ when IsPath(expression, "DefinitionDsl", "Header") => ScribeLegacyConstructor.Header,
            _ when IsPath(expression, "DescribeProvenance", "Unassessed") => ScribeLegacyConstructor.UnassessedProvenance,
            IdentifierNameSyntax { Identifier.ValueText: "LeanTheorem" } when importsDefinitionDsl => ScribeLegacyConstructor.LeanTheorem,
            IdentifierNameSyntax { Identifier.ValueText: "Header" } when importsDefinitionDsl => ScribeLegacyConstructor.Header,
            _ => null,
        };

    private static bool IsPath(ExpressionSyntax expression, params string[] identifiers)
    {
        for (var index = identifiers.Length - 1; index > 0; index--)
        {
            if (expression is not MemberAccessExpressionSyntax member
                || member.Name.Identifier.ValueText != identifiers[index]) return false;
            expression = member.Expression;
        }
        return expression is IdentifierNameSyntax identifier
            && identifier.Identifier.ValueText == identifiers[0];
    }

    private static string? RightmostIdentifier(NameSyntax? name) => name switch
    {
        SimpleNameSyntax simple => simple.Identifier.ValueText,
        QualifiedNameSyntax qualified => RightmostIdentifier(qualified.Right),
        AliasQualifiedNameSyntax alias => RightmostIdentifier(alias.Name),
        _ => null,
    };
}
