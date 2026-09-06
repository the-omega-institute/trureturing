using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace StrataLint.Engine;

internal static partial class ScribeTestSymbolBinder
{
    private static bool IsProductionReader(
        IMethodSymbol method,
        IReadOnlySet<string>? productionAssemblies) =>
        productionAssemblies?.Contains(method.ContainingAssembly.Name) == true;

    private static bool IsProductionRepositoryRead(
        IMethodSymbol method,
        SyntaxNode node,
        SemanticModel model,
        ScribeSemanticModelProvider semanticModels,
        IReadOnlySet<string>? productionAssemblies) =>
        IsProductionReader(method, productionAssemblies)
        && node is InvocationExpressionSyntax invocation
        && invocation.ArgumentList.Arguments.Any(argument =>
            ClassifyRepositoryRoot(
                argument.Expression,
                model,
                semanticModels,
                new HashSet<ISymbol>(SymbolEqualityComparer.Default))
                is not RepositoryRootClassification.NotRepositoryRoot);

    internal static bool IsRepositoryRootExpression(
        ExpressionSyntax expression,
        SemanticModel model,
        ScribeSemanticModelProvider semanticModels) => ClassifyRepositoryRoot(
            expression,
            model,
            semanticModels,
            new HashSet<ISymbol>(SymbolEqualityComparer.Default))
                == RepositoryRootClassification.RepositoryRoot;

    private static RepositoryRootClassification ClassifyRepositoryRoot(
        ExpressionSyntax expression,
        SemanticModel model,
        ScribeSemanticModelProvider semanticModels,
        HashSet<ISymbol> visited)
    {
        var findRootInvocations = expression.DescendantNodesAndSelf()
            .OfType<InvocationExpressionSyntax>()
            .Where(static invocation => invocation.Expression switch
            {
                SimpleNameSyntax { Identifier.ValueText: "FindRoot" } => true,
                MemberAccessExpressionSyntax { Name.Identifier.ValueText: "FindRoot" } => true,
                MemberBindingExpressionSyntax { Name.Identifier.ValueText: "FindRoot" } => true,
                _ => false,
            })
            .ToArray();
        if (expression.DescendantNodesAndSelf().OfType<MemberAccessExpressionSyntax>().Any(static member =>
                member.Name.Identifier.ValueText == "FullPath"
                && member.Expression is MemberAccessExpressionSyntax
                {
                    Name.Identifier.ValueText: "Root",
                }))
        {
            return RepositoryRootClassification.RepositoryRoot;
        }

        var expressionModel = semanticModels.ModelFor(expression, model);
        if (expressionModel is null)
        {
            return RepositoryRootClassification.Unknown;
        }
        model = expressionModel;

        if (findRootInvocations.Any(invocation =>
                model.GetSymbolInfo(invocation).Symbol is IMethodSymbol
                {
                    Name: "FindRoot",
                    ReturnType.SpecialType: SpecialType.System_String,
                }))
        {
            return RepositoryRootClassification.RepositoryRoot;
        }

        if (expression is not IdentifierNameSyntax identifier
            || model.GetSymbolInfo(identifier).Symbol is not { } symbol
            || !visited.Add(symbol))
        {
            return RepositoryRootClassification.NotRepositoryRoot;
        }

        var classification = symbol switch
        {
            ILocalSymbol local => ClassifyRepositoryRoot(
                LocalInitializers(local), model, semanticModels, visited),
            IFieldSymbol field => ClassifyRepositoryRoot(
                FieldInitializers(field), model, semanticModels, visited),
            IPropertySymbol property => ClassifyRepositoryRoot(
                PropertyInitializers(property), model, semanticModels, visited),
            _ => RepositoryRootClassification.NotRepositoryRoot,
        };
        return symbol is ILocalSymbol localSymbol
            && classification is not RepositoryRootClassification.RepositoryRoot
            && IsMarkerSearchRoot(localSymbol, model)
                ? RepositoryRootClassification.RepositoryRoot
                : classification;
    }

    private static RepositoryRootClassification ClassifyRepositoryRoot(
        IEnumerable<ExpressionSyntax> expressions,
        SemanticModel model,
        ScribeSemanticModelProvider semanticModels,
        HashSet<ISymbol> visited)
    {
        var classification = RepositoryRootClassification.NotRepositoryRoot;
        foreach (var expression in expressions)
        {
            var current = ClassifyRepositoryRoot(expression, model, semanticModels, visited);
            if (current == RepositoryRootClassification.RepositoryRoot) return current;
            if (current == RepositoryRootClassification.Unknown) classification = current;
        }
        return classification;
    }

    private enum RepositoryRootClassification
    {
        NotRepositoryRoot,
        RepositoryRoot,
        Unknown,
    }

    private static IEnumerable<ExpressionSyntax> LocalInitializers(ILocalSymbol local) =>
        local.DeclaringSyntaxReferences
            .Select(static reference => reference.GetSyntax())
            .OfType<VariableDeclaratorSyntax>()
            .Select(static variable => variable.Initializer?.Value)
            .Where(static value => value is not null)
            .Select(static value => value!);

    private static IEnumerable<ExpressionSyntax> FieldInitializers(IFieldSymbol field) =>
        field.DeclaringSyntaxReferences
            .Select(static reference => reference.GetSyntax())
            .OfType<VariableDeclaratorSyntax>()
            .Select(static variable => variable.Initializer?.Value)
            .Where(static value => value is not null)
            .Select(static value => value!);

    private static IEnumerable<ExpressionSyntax> PropertyInitializers(IPropertySymbol property) =>
        property.DeclaringSyntaxReferences
            .Select(static reference => reference.GetSyntax())
            .OfType<PropertyDeclarationSyntax>()
            .Select(static declaration => declaration.Initializer?.Value)
            .Where(static value => value is not null)
            .Select(static value => value!);

    private static bool IsMarkerSearchRoot(ILocalSymbol local, SemanticModel model)
    {
        var declaration = local.DeclaringSyntaxReferences
            .Select(static reference => reference.GetSyntax())
            .OfType<VariableDeclaratorSyntax>()
            .FirstOrDefault();
        var callable = declaration?.Ancestors().FirstOrDefault(static ancestor =>
            ancestor is BaseMethodDeclarationSyntax or AccessorDeclarationSyntax
                or LocalFunctionStatementSyntax);
        if (callable is null
            || declaration?.Initializer?.Value is not MemberAccessExpressionSyntax initializer
            || model.GetSymbolInfo(initializer).Symbol is not IPropertySymbol
            {
                Name: "BaseDirectory",
                ContainingType: { } appContext,
            }
            || appContext.ToDisplayString() != "System.AppContext")
        {
            return false;
        }

        return callable.DescendantNodes().OfType<WhileStatementSyntax>()
            .SelectMany(static loop => loop.Condition.DescendantNodesAndSelf()
                .OfType<InvocationExpressionSyntax>())
            .Where(invocation => model.GetSymbolInfo(invocation).Symbol is IMethodSymbol
            {
                Name: "Exists",
                ContainingType: { } type,
            } && type.ToDisplayString() == "System.IO.File")
            .SelectMany(static invocation => invocation.ArgumentList.Arguments)
            .SelectMany(static argument => argument.Expression.DescendantNodesAndSelf()
                .OfType<IdentifierNameSyntax>())
            .Any(identifier => SymbolEqualityComparer.Default.Equals(
                model.GetSymbolInfo(identifier).Symbol,
                local));
    }

    private static bool IsReflectionDispatch(IMethodSymbol method)
    {
        var type = method.ContainingType.ToDisplayString();
        return type.StartsWith("System.Reflection.", StringComparison.Ordinal)
            || type == "System.Type" && method.Name.StartsWith("Get", StringComparison.Ordinal)
            || type == "System.Activator" && method.Name == "CreateInstance";
    }
}
