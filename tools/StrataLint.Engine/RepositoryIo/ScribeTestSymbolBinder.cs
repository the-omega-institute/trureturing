using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace StrataLint.Engine;

internal sealed record ScribeParsedSource(
    SyntaxNode Root,
    IReadOnlyList<ScribeBoundCallable> Callables);

internal sealed class ScribeBoundCallable
{
    internal ScribeBoundCallable(
        string path,
        string partitionKey,
        string typeName,
        string name,
        bool isTest,
        bool isStaticallySkipped,
        bool isDiscoveryConditional,
        SyntaxNode syntax,
        SemanticModel semanticModel,
        ScribeSemanticModelProvider semanticModels,
        IReadOnlyList<SyntaxNode> inspectionNodes)
    {
        Path = path;
        PartitionKey = partitionKey;
        TypeName = typeName;
        Name = name;
        IsTest = isTest;
        IsStaticallySkipped = isStaticallySkipped;
        IsDiscoveryConditional = isDiscoveryConditional;
        Syntax = syntax;
        SemanticModel = semanticModel;
        SemanticModels = semanticModels;
        InspectionNodes = inspectionNodes;
    }

    internal string Path { get; }
    internal string PartitionKey { get; }
    internal string TypeName { get; }
    internal string Name { get; }
    internal bool IsTest { get; }
    internal bool IsStaticallySkipped { get; }
    internal bool IsDiscoveryConditional { get; }
    internal SyntaxNode Syntax { get; }
    internal SemanticModel SemanticModel { get; }
    internal ScribeSemanticModelProvider SemanticModels { get; }
    internal IReadOnlyList<SyntaxNode> InspectionNodes { get; }
    internal HashSet<ScribeBoundCallable> Targets { get; } = [];
    internal HashSet<TestMapUnknownReason> BindingUnknownReasons { get; } = [];

    internal bool ContainsLine(int line) => InspectionNodes.Any(node =>
    {
        var span = node.GetLocation().GetLineSpan();
        return line >= span.StartLinePosition.Line + 1
            && line <= span.EndLinePosition.Line + 1;
    });
}

internal static class ScribeTestSymbolBinder
{
    internal static IReadOnlyList<ScribeParsedSource> Bind(
        IEnumerable<TestMapSource> sourceFiles,
        out IReadOnlyList<ScribeMetadataDegradation> metadataDegradations,
        IReadOnlySet<string>? productionAssemblies = null,
        ScribeProjectCompilationContext? compilationContext = null)
    {
        var sources = sourceFiles.ToArray();
        var compilations = ScribeProjectCompilationBuilder.Build(sources, compilationContext);
        metadataDegradations = compilations
            .Select(static project => project.MetadataDegradation)
            .Where(static degradation => degradation is not null)
            .Select(static degradation => degradation!)
            .DistinctBy(static degradation => degradation.ProjectPath)
            .OrderBy(static degradation => degradation.ProjectPath, StringComparer.Ordinal)
            .ToArray();
        var semanticModels = new ScribeSemanticModelProvider();
        foreach (var project in compilations) semanticModels.Add(project.Compilation);
        var callablesBySymbol = new ScribeCallableIndex();
        var symbolsByCallable = new Dictionary<ScribeBoundCallable, IMethodSymbol>();
        var parsed = new List<ScribeParsedSource>();

        foreach (var project in compilations)
        {
            foreach (var item in project.GovernedSources)
            {
                var model = project.Compilation.GetSemanticModel(item.Tree);
                var root = item.Tree.GetRoot();
                var roots = new List<ScribeBoundCallable>();
                foreach (var declaration in root.DescendantNodes().OfType<BaseMethodDeclarationSyntax>())
                {
                    if (model.GetDeclaredSymbol(declaration) is IMethodSymbol symbol)
                    {
                        AddCallable(item.Source, declaration, symbol, model, semanticModels, callablesBySymbol, symbolsByCallable, roots);
                    }
                }
                foreach (var declaration in root.DescendantNodes().OfType<AccessorDeclarationSyntax>())
                {
                    if (model.GetDeclaredSymbol(declaration) is IMethodSymbol symbol)
                    {
                        AddCallable(item.Source, declaration, symbol, model, semanticModels, callablesBySymbol, symbolsByCallable, roots);
                    }
                }
                foreach (var declaration in root.DescendantNodes().OfType<LocalFunctionStatementSyntax>())
                {
                    if (model.GetDeclaredSymbol(declaration) is IMethodSymbol symbol)
                    {
                        AddCallable(item.Source, declaration, symbol, model, semanticModels, callablesBySymbol, symbolsByCallable, roots);
                    }
                }
                foreach (var declaration in root.DescendantNodes().OfType<BasePropertyDeclarationSyntax>())
                {
                    if (model.GetDeclaredSymbol(declaration) is IPropertySymbol property)
                    {
                        AddPropertyAccessors(
                            item.Source,
                            declaration,
                            property,
                            model,
                            semanticModels,
                            callablesBySymbol,
                            symbolsByCallable,
                            roots);
                    }
                }
                foreach (var declaration in root.DescendantNodes().OfType<TypeDeclarationSyntax>())
                {
                    if (model.GetDeclaredSymbol(declaration) is not INamedTypeSymbol type) continue;
                    foreach (var constructor in type.InstanceConstructors)
                    {
                        if (!callablesBySymbol.Contains(constructor)
                            && (constructor.IsImplicitlyDeclared
                                || constructor.DeclaringSyntaxReferences.Any(reference =>
                                    reference.GetSyntax() == declaration)))
                        {
                            AddCallable(
                                item.Source,
                                declaration,
                                constructor,
                                model,
                                semanticModels,
                                callablesBySymbol,
                                symbolsByCallable,
                                roots);
                        }
                    }
                }
                if (project.MetadataDegradation is not null)
                {
                    foreach (var test in roots.Where(static callable => callable.IsTest))
                    {
                        test.BindingUnknownReasons.Add(TestMapUnknownReason.MetadataUnavailable);
                    }
                }
                parsed.Add(new ScribeParsedSource(root, roots));
            }
        }

        foreach (var (callable, symbol) in symbolsByCallable)
        {
            BindEdges(
                callable,
                symbol,
                callable.SemanticModel,
                callablesBySymbol,
                productionAssemblies);
        }

        return parsed;
    }

    private static void AddCallable(
        TestMapSource source,
        SyntaxNode declaration,
        IMethodSymbol symbol,
        SemanticModel model,
        ScribeSemanticModelProvider semanticModels,
        ScribeCallableIndex callablesBySymbol,
        Dictionary<ScribeBoundCallable, IMethodSymbol> symbolsByCallable,
        List<ScribeBoundCallable> roots)
    {
        var normalized = ScribeCallableIndex.Normalize(symbol);
        if (callablesBySymbol.Contains(normalized)) return;
        var isTest = declaration is MethodDeclarationSyntax method && IsTestMethod(method, model);
        var callable = new ScribeBoundCallable(
            source.Path,
            source.PartitionKey,
            symbol.ContainingType?.Name ?? "<global>",
            symbol.Name,
            isTest,
            isTest && IsStaticallySkipped((MethodDeclarationSyntax)declaration, model),
            isTest && IsDiscoveryConditional(
                (MethodDeclarationSyntax)declaration,
                model,
                semanticModels),
            declaration,
            model,
            semanticModels,
            InspectionNodes(declaration));
        callablesBySymbol.Add(normalized, callable);
        symbolsByCallable.Add(callable, normalized);
        roots.Add(callable);
    }

    private static void AddPropertyAccessors(
        TestMapSource source,
        BasePropertyDeclarationSyntax declaration,
        IPropertySymbol property,
        SemanticModel model,
        ScribeSemanticModelProvider semanticModels,
        ScribeCallableIndex callablesBySymbol,
        Dictionary<ScribeBoundCallable, IMethodSymbol> symbolsByCallable,
        List<ScribeBoundCallable> roots)
    {
        foreach (var accessor in new[] { property.GetMethod, property.SetMethod })
        {
            if (accessor is not null)
            {
                AddCallable(
                    source,
                    declaration,
                    accessor,
                    model,
                    semanticModels,
                    callablesBySymbol,
                    symbolsByCallable,
                    roots);
            }
        }
    }

    private static void BindEdges(
        ScribeBoundCallable callable,
        IMethodSymbol symbol,
        SemanticModel model,
        ScribeCallableIndex callablesBySymbol,
        IReadOnlySet<string>? productionAssemblies)
    {
        if (callable.IsTest)
        {
            AddConstructors(symbol.ContainingType, callable.Targets, callablesBySymbol);
            foreach (var fixture in symbol.ContainingType.AllInterfaces
                         .Where(static type => type.OriginalDefinition.ToDisplayString() == "Xunit.IClassFixture<TFixture>")
                         .SelectMany(static type => type.TypeArguments)
                         .OfType<INamedTypeSymbol>())
            {
                AddConstructors(fixture, callable.Targets, callablesBySymbol);
            }
        }

        foreach (var node in callable.InspectionNodes)
        {
            switch (node)
            {
                case InvocationExpressionSyntax invocation:
                    if (model.GetOperation(invocation) is INameOfOperation) break;
                    BindMethodNode(
                        invocation,
                        callable,
                        model,
                        callablesBySymbol,
                        productionAssemblies,
                        failWhenUnresolved: true);
                    break;
                case ObjectCreationExpressionSyntax or ImplicitObjectCreationExpressionSyntax
                    or ConstructorInitializerSyntax or AttributeSyntax:
                    BindMethodNode(
                        node,
                        callable,
                        model,
                        callablesBySymbol,
                        productionAssemblies,
                        failWhenUnresolved: node is not AttributeSyntax attribute
                            || IsTestAttribute(attribute, model));
                    break;
                case MemberAccessExpressionSyntax member when member.Parent is not InvocationExpressionSyntax:
                    BindMemberNode(member, callable, model, callablesBySymbol);
                    break;
                case IdentifierNameSyntax identifier when identifier.Parent is not InvocationExpressionSyntax:
                    if (!IsInsideNameof(identifier, model))
                    {
                        BindMemberNode(identifier, callable, model, callablesBySymbol);
                    }
                    break;
                case ElementAccessExpressionSyntax element:
                    BindMemberNode(element, callable, model, callablesBySymbol);
                    break;
            }
        }
    }

    private static void BindMethodNode(
        SyntaxNode node,
        ScribeBoundCallable caller,
        SemanticModel model,
        ScribeCallableIndex callablesBySymbol,
        IReadOnlySet<string>? productionAssemblies,
        bool failWhenUnresolved)
    {
        var info = model.GetSymbolInfo(node);
        var method = info.Symbol as IMethodSymbol ?? model.GetOperation(node) switch
        {
            IInvocationOperation invocation => invocation.TargetMethod,
            IObjectCreationOperation creation => creation.Constructor,
            _ => null,
        };
        if (method is not null)
        {
            AddBoundMethod(
                method,
                node,
                caller,
                model,
                callablesBySymbol,
                productionAssemblies);
            return;
        }

        var candidates = info.CandidateSymbols.OfType<IMethodSymbol>().ToArray();
        if (candidates.Length == 1
            && IsProductionRepositoryRead(candidates[0], node, model, productionAssemblies))
        {
            caller.BindingUnknownReasons.Add(TestMapUnknownReason.IndirectViaProductionLoader);
        }
        else if (failWhenUnresolved || candidates.Length != 0)
        {
            caller.BindingUnknownReasons.Add(TestMapUnknownReason.Other);
        }
    }

    private static void AddBoundMethod(
        IMethodSymbol method,
        SyntaxNode node,
        ScribeBoundCallable caller,
        SemanticModel model,
        ScribeCallableIndex callablesBySymbol,
        IReadOnlySet<string>? productionAssemblies)
    {
        var normalized = ScribeCallableIndex.Normalize(method);
        if (callablesBySymbol.TryGetValue(normalized, out var target))
        {
            caller.Targets.Add(target);
        }
        else if (IsProductionRepositoryRead(normalized, node, model, productionAssemblies))
        {
            caller.BindingUnknownReasons.Add(TestMapUnknownReason.IndirectViaProductionLoader);
        }
        else if (IsReflectionDispatch(normalized))
        {
            caller.BindingUnknownReasons.Add(TestMapUnknownReason.Other);
        }
    }

    private static void BindMemberNode(
        SyntaxNode node,
        ScribeBoundCallable caller,
        SemanticModel model,
        ScribeCallableIndex callablesBySymbol)
    {
        switch (model.GetSymbolInfo(node).Symbol)
        {
            case IMethodSymbol method:
                if (callablesBySymbol.TryGetValue(method, out var methodTarget))
                    caller.Targets.Add(methodTarget);
                break;
            case IPropertySymbol property:
                AddAccessor(property.GetMethod, caller.Targets, callablesBySymbol);
                AddAccessor(property.SetMethod, caller.Targets, callablesBySymbol);
                break;
            case IEventSymbol @event:
                AddAccessor(@event.AddMethod, caller.Targets, callablesBySymbol);
                AddAccessor(@event.RemoveMethod, caller.Targets, callablesBySymbol);
                break;
        }
    }

    private static void AddConstructors(
        INamedTypeSymbol type,
        HashSet<ScribeBoundCallable> targets,
        ScribeCallableIndex callablesBySymbol)
    {
        foreach (var constructor in type.InstanceConstructors)
            AddAccessor(constructor, targets, callablesBySymbol);
    }

    private static void AddAccessor(
        IMethodSymbol? method,
        HashSet<ScribeBoundCallable> targets,
        ScribeCallableIndex callablesBySymbol)
    {
        if (method is not null && callablesBySymbol.TryGetValue(method, out var target))
            targets.Add(target);
    }

    private static IReadOnlyList<SyntaxNode> InspectionNodes(SyntaxNode declaration)
    {
        if (declaration is TypeDeclarationSyntax type)
        {
            return type.Members.SelectMany(static member => member switch
            {
                FieldDeclarationSyntax field => field.Declaration.Variables
                    .Select(static variable => variable.Initializer?.Value)
                    .Where(static value => value is not null)
                    .SelectMany(static value => value!.DescendantNodesAndSelf()),
                PropertyDeclarationSyntax property when property.Initializer is not null =>
                    property.Initializer.Value.DescendantNodesAndSelf(),
                EventFieldDeclarationSyntax field => field.Declaration.Variables
                    .Select(static variable => variable.Initializer?.Value)
                    .Where(static value => value is not null)
                    .SelectMany(static value => value!.DescendantNodesAndSelf()),
                _ => [],
            }).ToArray();
        }

        return declaration.DescendantNodesAndSelf(node =>
            ReferenceEquals(node, declaration)
            || node is not LocalFunctionStatementSyntax
                and not TypeDeclarationSyntax).ToArray();
    }

    private static bool IsTestMethod(MethodDeclarationSyntax method, SemanticModel model) =>
        method.AttributeLists.SelectMany(static list => list.Attributes)
            .Any(attribute => IsTestAttribute(attribute, model));

    private static bool IsTestAttribute(AttributeSyntax attribute, SemanticModel model) =>
        Symbols(model.GetSymbolInfo(attribute)).OfType<IMethodSymbol>()
            .Any(static constructor => IsXunitTestAttribute(constructor.ContainingType));

    private static IEnumerable<ISymbol> Symbols(SymbolInfo info)
    {
        if (info.Symbol is not null) yield return info.Symbol;
        foreach (var candidate in info.CandidateSymbols) yield return candidate;
    }

    private static bool IsXunitTestAttribute(INamedTypeSymbol? type)
    {
        for (var current = type; current is not null; current = current.BaseType)
        {
            var display = current.ToDisplayString();
            if (display is "Xunit.FactAttribute" or "Xunit.TheoryAttribute") return true;
        }
        return false;
    }

    private static bool IsStaticallySkipped(MethodDeclarationSyntax method, SemanticModel model) =>
        method.AttributeLists.SelectMany(static list => list.Attributes)
            .Where(attribute => IsTestAttribute(attribute, model))
            .Any(static attribute => attribute.ArgumentList?.Arguments.Any(static argument =>
                argument.NameEquals?.Name.Identifier.ValueText == "Skip"
                && !argument.Expression.IsKind(SyntaxKind.NullLiteralExpression)) == true);

    private static bool IsDiscoveryConditional(
        MethodDeclarationSyntax method,
        SemanticModel model,
        ScribeSemanticModelProvider semanticModels) => method.AttributeLists
        .SelectMany(static list => list.Attributes)
        .Where(attribute => IsTestAttribute(attribute, model))
        .SelectMany(attribute => Symbols(model.GetSymbolInfo(attribute)).OfType<IMethodSymbol>())
        .SelectMany(static constructor => constructor.DeclaringSyntaxReferences)
        .Select(static reference => reference.GetSyntax())
        .Any(declaration => ConstructorAssignsFactSkip(declaration, model, semanticModels));

    private static bool ConstructorAssignsFactSkip(
        SyntaxNode declaration,
        SemanticModel fallback,
        ScribeSemanticModelProvider semanticModels)
    {
        var model = semanticModels.ModelFor(declaration, fallback);
        return model is not null && declaration.DescendantNodes()
            .OfType<AssignmentExpressionSyntax>()
            .Where(static assignment => assignment.IsKind(SyntaxKind.SimpleAssignmentExpression))
            .Any(assignment => model.GetSymbolInfo(assignment.Left).Symbol is IPropertySymbol
            {
                Name: "Skip",
                ContainingType: { } type,
            } && type.ToDisplayString() == "Xunit.FactAttribute");
    }

    private static bool IsInsideNameof(SyntaxNode node, SemanticModel model) => node.Ancestors()
        .OfType<InvocationExpressionSyntax>()
        .Any(invocation => model.GetOperation(invocation) is INameOfOperation);

    private static bool IsProductionReader(
        IMethodSymbol method,
        IReadOnlySet<string>? productionAssemblies) =>
        productionAssemblies?.Contains(method.ContainingAssembly.Name) == true;

    private static bool IsProductionRepositoryRead(
        IMethodSymbol method,
        SyntaxNode node,
        SemanticModel model,
        IReadOnlySet<string>? productionAssemblies) =>
        IsProductionReader(method, productionAssemblies)
        && node is InvocationExpressionSyntax invocation
        && invocation.ArgumentList.Arguments.Any(argument =>
            IsRepositoryRootExpression(argument.Expression, model));

    internal static bool IsRepositoryRootExpression(
        ExpressionSyntax expression,
        SemanticModel model) => IsRepositoryRoot(
            expression,
            model,
            new HashSet<ISymbol>(SymbolEqualityComparer.Default));

    private static bool IsRepositoryRoot(
        ExpressionSyntax expression,
        SemanticModel model,
        HashSet<ISymbol> visited)
    {
        if (expression.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>().Any(invocation =>
                model.GetSymbolInfo(invocation).Symbol is IMethodSymbol
                {
                    Name: "FindRoot",
                    ReturnType.SpecialType: SpecialType.System_String,
                }))
        {
            return true;
        }

        if (expression.DescendantNodesAndSelf().OfType<MemberAccessExpressionSyntax>().Any(static member =>
                member.Name.Identifier.ValueText == "FullPath"
                && member.Expression is MemberAccessExpressionSyntax
                {
                    Name.Identifier.ValueText: "Root",
                }))
        {
            return true;
        }

        if (expression is not IdentifierNameSyntax identifier
            || model.GetSymbolInfo(identifier).Symbol is not { } symbol
            || !visited.Add(symbol))
        {
            return false;
        }

        return symbol switch
        {
            ILocalSymbol local => LocalInitializers(local).Any(value =>
                    IsRepositoryRoot(value, model, visited))
                || IsMarkerSearchRoot(local, model),
            IFieldSymbol field => FieldInitializers(field).Any(value =>
                IsRepositoryRoot(value, model, visited)),
            IPropertySymbol property => PropertyInitializers(property).Any(value =>
                IsRepositoryRoot(value, model, visited)),
            _ => false,
        };
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
