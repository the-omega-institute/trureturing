using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.Engine;

internal static class ScribePathProvenance
{
    internal static bool IsNonRepository(
        ExpressionSyntax expression,
        SemanticModel model,
        ScribeSemanticModelProvider models) => IsNonRepository(
            expression,
            model,
            models,
            new HashSet<ISymbol>(SymbolEqualityComparer.Default));

    private static bool IsNonRepository(
        ExpressionSyntax expression,
        SemanticModel model,
        ScribeSemanticModelProvider models,
        HashSet<ISymbol> visited)
    {
        if (models.ModelFor(expression, model) is not { } expressionModel) return false;
        model = expressionModel;
        if (expression is InvocationExpressionSyntax invocation
            && model.GetSymbolInfo(invocation).Symbol is IMethodSymbol method)
        {
            var owner = method.ContainingType.ToDisplayString();
            if (owner == "System.IO.Directory" && method.Name == "CreateTempSubdirectory")
                return true;
            if (owner == "System.IO.Path"
                && method.Name is "Combine" or "GetFullPath"
                && invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression is { } first)
                return IsNonRepository(first, model, models, visited);
            if (method.Locations.Any(static location => location.IsInSource))
                return SourceMethodReturns(method, model, models, visited);
        }

        if (expression is MemberAccessExpressionSyntax member
            && model.GetSymbolInfo(member).Symbol is IPropertySymbol
            {
                Name: "FullName",
                ContainingType: { } propertyOwner,
            }
            && IsFileSystemInfo(propertyOwner))
            return IsNonRepository(member.Expression, model, models, visited);

        var symbol = model.GetSymbolInfo(expression).Symbol;
        if (symbol is IParameterSymbol parameter && IsLambdaPath(parameter, model, models, visited))
            return true;
        if (symbol is not ILocalSymbol and not IFieldSymbol and not IPropertySymbol
            || !visited.Add(symbol))
            return false;

        try
        {
            var values = AssignedValues(symbol, model, models).ToArray();
            return values.Length != 0
                && values.All(value => IsNonRepository(value, model, models, visited));
        }
        finally
        {
            visited.Remove(symbol);
        }
    }

    private static bool IsLambdaPath(
        IParameterSymbol parameter,
        SemanticModel model,
        ScribeSemanticModelProvider models,
        HashSet<ISymbol> visited)
    {
        var sources = parameter.DeclaringSyntaxReferences
            .Select(static reference => reference.GetSyntax())
            .Select(static syntax => syntax.AncestorsAndSelf().OfType<LambdaExpressionSyntax>().FirstOrDefault())
            .Where(static lambda => lambda is not null)
            .Select(static lambda => lambda!.Parent)
            .OfType<ArgumentSyntax>()
            .Select(static argument => argument.Parent?.Parent)
            .OfType<InvocationExpressionSyntax>()
            .Select(static invocation => (invocation.Expression as MemberAccessExpressionSyntax)?.Expression)
            .Where(static source => source is not null)
            .Select(static source => source!)
            .ToArray();
        return sources.Length != 0
            && sources.All(source => IsNonRepositorySequence(source, model, models, visited));
    }

    private static bool IsNonRepositorySequence(
        ExpressionSyntax expression,
        SemanticModel model,
        ScribeSemanticModelProvider models,
        HashSet<ISymbol> visited)
    {
        if (models.ModelFor(expression, model) is not { } expressionModel) return false;
        model = expressionModel;
        if (expression is not InvocationExpressionSyntax invocation
            || model.GetSymbolInfo(invocation).Symbol is not IMethodSymbol method)
            return false;
        var normalized = Normalize(method);
        if (normalized.ContainingType.ToDisplayString() == "System.IO.Directory"
            && normalized.Name == "EnumerateFiles"
            && invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression is { } root)
            return IsNonRepository(root, model, models, visited);
        return normalized.ContainingType.ToDisplayString() == "System.Linq.Enumerable"
            && normalized.Name is "Distinct" or "Order" or "OrderBy" or "OrderByDescending"
                or "Reverse" or "Skip" or "Take" or "ThenBy" or "ThenByDescending" or "Where"
            && invocation.Expression is MemberAccessExpressionSyntax { Expression: var source }
            && IsNonRepositorySequence(source, model, models, visited);
    }

    private static bool SourceMethodReturns(
        IMethodSymbol method,
        SemanticModel model,
        ScribeSemanticModelProvider models,
        HashSet<ISymbol> visited)
    {
        method = Normalize(method);
        if (!visited.Add(method)) return false;
        try
        {
            var values = method.DeclaringSyntaxReferences
                .Select(static reference => reference.GetSyntax())
                .SelectMany(ReturnValues)
                .ToArray();
            return values.Length != 0
                && values.All(value => IsNonRepository(value, model, models, visited));
        }
        finally
        {
            visited.Remove(method);
        }
    }

    private static IEnumerable<ExpressionSyntax> ReturnValues(SyntaxNode declaration)
    {
        var expressionBody = declaration switch
        {
            MethodDeclarationSyntax method => method.ExpressionBody?.Expression,
            LocalFunctionStatementSyntax local => local.ExpressionBody?.Expression,
            OperatorDeclarationSyntax operation => operation.ExpressionBody?.Expression,
            ConversionOperatorDeclarationSyntax conversion => conversion.ExpressionBody?.Expression,
            AccessorDeclarationSyntax accessor => accessor.ExpressionBody?.Expression,
            _ => null,
        };
        if (expressionBody is not null) yield return expressionBody;
        foreach (var statement in declaration.DescendantNodes(node =>
                     ReferenceEquals(node, declaration)
                     || node is not LocalFunctionStatementSyntax
                         and not AnonymousFunctionExpressionSyntax
                         and not TypeDeclarationSyntax)
                 .OfType<ReturnStatementSyntax>())
            if (statement.Expression is not null) yield return statement.Expression;
    }

    private static IEnumerable<ExpressionSyntax> AssignedValues(
        ISymbol symbol,
        SemanticModel model,
        ScribeSemanticModelProvider models)
    {
        foreach (var syntax in symbol.DeclaringSyntaxReferences.Select(static reference => reference.GetSyntax()))
        {
            if (syntax is VariableDeclaratorSyntax { Initializer.Value: { } initial }) yield return initial;
            if (syntax is PropertyDeclarationSyntax property)
            {
                if (property.Initializer?.Value is { } initializer) yield return initializer;
                if (property.ExpressionBody?.Expression is { } expression) yield return expression;
                foreach (var value in property.AccessorList?.Accessors
                             .Where(static accessor => accessor.IsKind(SyntaxKind.GetAccessorDeclaration))
                             .SelectMany(ReturnValues) ?? [])
                    yield return value;
            }
        }

        var scopes = symbol switch
        {
            ILocalSymbol => symbol.DeclaringSyntaxReferences.Select(static reference =>
                reference.GetSyntax().Ancestors().First(static node =>
                    node is BaseMethodDeclarationSyntax or AccessorDeclarationSyntax or LocalFunctionStatementSyntax)),
            _ => symbol.ContainingType?.DeclaringSyntaxReferences.Select(static reference => reference.GetSyntax()) ?? [],
        };
        foreach (var assignment in scopes.SelectMany(static scope => scope.DescendantNodes()
                     .OfType<AssignmentExpressionSyntax>()))
        {
            var assignmentModel = models.ModelFor(assignment, model);
            if (assignmentModel is not null && SymbolEqualityComparer.Default.Equals(
                    assignmentModel.GetSymbolInfo(assignment.Left).Symbol,
                    symbol))
                yield return assignment.Right;
        }
    }

    private static bool IsFileSystemInfo(INamedTypeSymbol type)
    {
        for (var current = type; current is not null; current = current.BaseType)
            if (current.ToDisplayString() == "System.IO.FileSystemInfo") return true;
        return false;
    }

    private static IMethodSymbol Normalize(IMethodSymbol method) =>
        (method.ReducedFrom ?? method).OriginalDefinition;
}
