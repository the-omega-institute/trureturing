using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.Scribe;

internal sealed partial class RelationSyntaxEvaluator
{
    private sealed record ProjectedValue(object? Value, object? Source);

    private object? ResolveProjectedValue(ProjectedValue projected)
    {
        if (readingRelations && knownValueDepth > 0) ResolveBinding(projected.Source);
        return projected.Value;
    }

    private object?[] ProjectSequence(ExpressionSyntax node, IMethodSymbol method,
        Dictionary<string, object?> arguments, Dictionary<ISymbol, object?> scope)
    {
        var sourceBinding = method.ReducedFrom is not null
            && node is InvocationExpressionSyntax { Expression: MemberAccessExpressionSyntax member }
            ? new Binding(member.Expression, scope) : arguments.GetValueOrDefault("source");
        object? source;
        try
        {
            source = ResolveBinding(sourceBinding);
        }
        catch (RelationSyntaxException exception) when (exception.Failure.Shape != "IgnoredWrite")
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
                [parameter] = new ProjectedValue(item, sourceBinding),
            };
            var value = Eval(body, nested);
            projected.Add(value);
        }
        return projected.ToArray();
    }
}
