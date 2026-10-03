using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.Scribe;

internal sealed partial class RelationSyntaxEvaluator
{
    private bool readingRelations;
    private readonly Dictionary<ISymbol, SyntaxNode> discriminantWrites = new(SymbolEqualityComparer.Default);

    private bool IsConstantDiscriminantField(IFieldSymbol field, ExpressionSyntax initializer) =>
        field.IsStatic && field.IsReadOnly && (Model(initializer).GetConstantValue(initializer).HasValue
            || readingNullness && initializer is InvocationExpressionSyntax invocation
                && Model(invocation).GetSymbolInfo(invocation).Symbol is IMethodSymbol method
                && IsNonNullRelationFactory(method)
                && invocation.ArgumentList.Arguments.All(argument => Model(argument).GetConstantValue(argument.Expression).HasValue))
        && !initializer.DescendantNodesAndSelf().OfType<ExpressionSyntax>().Any(expression =>
            Model(expression).GetSymbolInfo(expression).Symbol is IFieldSymbol or IPropertySymbol);

    private static bool IsNonNullRelationFactory(IMethodSymbol method) =>
        method.DeclaringSyntaxReferences.Length == 0
        && method.ContainingType.ToDisplayString().StartsWith("StrataLint.Scribe.", StringComparison.Ordinal)
        && IsRelationType(method.ReturnType) && method.ReturnType.SpecialType != SpecialType.System_String;

    private void ValidateDiscriminantWrite(ExpressionSyntax expression)
    {
        var symbol = Model(expression).GetSymbolInfo(expression).Symbol;
        if (symbol is ILocalSymbol or IParameterSymbol && discriminantWrites.TryGetValue(symbol, out var write))
            throw Reject(write, "IgnoredWrite", "Branch discriminant locals and parameters must be single assignment.");
    }

    private void CollectDiscriminantWrites(SyntaxNode entryMethod)
    {
        var visited = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        Collect(entryMethod);

        void Collect(SyntaxNode helper)
        {
            foreach (var node in helper.DescendantNodes())
            {
                var target = node switch
                {
                    AssignmentExpressionSyntax assignment => assignment.Left,
                    PrefixUnaryExpressionSyntax { OperatorToken.ValueText: "++" or "--" } prefix => prefix.Operand,
                    PostfixUnaryExpressionSyntax { OperatorToken.ValueText: "++" or "--" } postfix => postfix.Operand,
                    ArgumentSyntax argument when argument.RefKindKeyword.IsKind(SyntaxKind.RefKeyword)
                        || argument.RefKindKeyword.IsKind(SyntaxKind.OutKeyword) => argument.Expression,
                    _ => null,
                };
                if (target is not null)
                    foreach (var symbol in WrittenSymbols(target)) discriminantWrites.TryAdd(symbol, node);
                if (node is InvocationExpressionSyntax invocation
                    && Model(invocation).GetSymbolInfo(invocation).Symbol is IMethodSymbol method
                    && method.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is { } declaration
                    && declaration is MethodDeclarationSyntax or LocalFunctionStatementSyntax && visited.Add(method))
                    Collect(declaration);
            }
        }
    }

    private IEnumerable<ISymbol> WrittenSymbols(ExpressionSyntax target)
    {
        if (target is TupleExpressionSyntax tuple)
        {
            foreach (var argument in tuple.Arguments)
                foreach (var symbol in WrittenSymbols(argument.Expression)) yield return symbol;
        }
        else if (Model(target).GetSymbolInfo(target).Symbol is { } symbol) yield return symbol;
    }
}
