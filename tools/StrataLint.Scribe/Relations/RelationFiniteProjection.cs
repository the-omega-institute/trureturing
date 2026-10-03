using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.Scribe;

internal sealed partial class RelationSyntaxEvaluator
{
    private object?[] ProjectSequence(ExpressionSyntax node, IMethodSymbol method,
        Dictionary<string, object?> arguments, Dictionary<ISymbol, object?> scope)
    {
        object? source;
        try
        {
            source = method.ReducedFrom is not null
                && node is InvocationExpressionSyntax { Expression: MemberAccessExpressionSyntax member }
                ? Eval(member.Expression, scope) : ResolveBinding(arguments.GetValueOrDefault("source"));
        }
        catch (RelationSyntaxException)
        {
            throw Reject(node, "UnsupportedInvocation", "Projection source is not a statically known finite collection.");
        }
        if (source is not object?[] items)
            throw Reject(node, "UnsupportedInvocation", "Projection requires a statically known finite collection.");
        if (method.Name == "ToArray") return items;
        if (arguments.GetValueOrDefault("selector")
            is not Binding { Expression: LambdaExpressionSyntax lambda } binding)
            throw Reject(node, "UnsupportedInvocation", "Projection requires an expression lambda.");
        var parameters = lambda switch
        {
            SimpleLambdaExpressionSyntax simple => new[] { simple.Parameter },
            ParenthesizedLambdaExpressionSyntax parenthesized => parenthesized.ParameterList.Parameters.ToArray(),
            _ => [],
        };
        if (parameters.Length != 1 || lambda.Body is not ExpressionSyntax body
            || arguments.ContainsKey("resultSelector"))
            throw Reject(node, "UnsupportedInvocation", "Only one-parameter expression projections are supported.");
        var parameter = Model(parameters[0]).GetDeclaredSymbol(parameters[0])
            ?? throw Reject(node, "UnsupportedInvocation", "Projection parameter has no symbol.");
        var projected = new List<object?>();
        foreach (var item in items)
        {
            var nested = new Dictionary<ISymbol, object?>(binding.Scope, SymbolEqualityComparer.Default)
            {
                [parameter] = item,
            };
            var value = Eval(body, nested);
            projected.Add(value);
        }
        return projected.ToArray();
    }
}
