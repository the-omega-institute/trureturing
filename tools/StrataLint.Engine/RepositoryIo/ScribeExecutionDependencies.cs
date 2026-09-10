using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace StrataLint.Engine;

internal sealed record BoundTestScope(string Project, string Scope, string[] Methods,
    string[] RuntimeInputs, string[] Edges, string[] Unknown);

// Execution closure is deliberately separate from Scribe's known/unknown debt.
// It consumes the same compiler-bound calls, before relevance pruning. The
// supported leaf semantics below are scalar CLR operations and xUnit v2 scalar
// assertions. An unmodelled library call is an unknown, never a pure-call guess.
internal static class ScribeExecutionDependencies
{
    internal static string[] CompilationUnknown(Microsoft.CodeAnalysis.CSharp.CSharpCompilation compilation)
    {
        var unknown = new SortedSet<string>(StringComparer.Ordinal);
        if (compilation.GetDiagnostics().Any(diagnostic => diagnostic.Severity == DiagnosticSeverity.Error))
            unknown.Add("compiler:semantic-errors:" + compilation.AssemblyName);
        // xUnit discovers these contracts regardless of the assembly defining
        // the attribute. Their lifecycle is outside the test-callable closure.
        var contracts = new[] { "Xunit.Sdk.ITestFrameworkAttribute", "Xunit.Sdk.ITraitAttribute",
            "Xunit.Sdk.BeforeAfterTestAttribute", "Xunit.CollectionBehaviorAttribute",
            "Xunit.TestCaseOrdererAttribute", "Xunit.TestCollectionOrdererAttribute" }
            .Select(compilation.GetTypeByMetadataName).OfType<INamedTypeSymbol>()
            .ToHashSet(SymbolEqualityComparer.Default);
        foreach (var attribute in compilation.Assembly.GetAttributes())
            for (var type = attribute.AttributeClass; type is not null; type = type.BaseType)
                if (contracts.Contains(type) || type.AllInterfaces.Any(contracts.Contains))
                    unknown.Add("test-lifecycle:assembly-adapter-attribute");
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var declaration in tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>())
                if (model.GetDeclaredSymbol(declaration) is IMethodSymbol method && method.GetAttributes().Any(attribute =>
                        attribute.AttributeClass?.ToDisplayString() == "System.Runtime.CompilerServices.ModuleInitializerAttribute"))
                    unknown.Add("runtime:module-initializer:" + method.ToDisplayString());
        }
        return unknown.ToArray();
    }

    internal static BoundTestScope[] Derive(ScribeProjectCompilationContext context, IReadOnlySet<string> tests)
    {
        var sources = context.Projects.Where(project => tests.Contains(project.Path))
            .SelectMany(project => project.Sources.Select(source => new TestMapSource(source.Path, source.Content, project.Path)));
        var parsed = ScribeTestSymbolBinder.Bind(sources, ScribeBindingStrategy.Demand, compilationContext: context);
        return parsed.SelectMany(source => source.Callables).Where(callable => callable.IsTest)
            .GroupBy(callable => (callable.PartitionKey, TypeName(callable.Symbol!.ContainingType)))
            .Select(group => Scope(group.Key.PartitionKey, group.Key.Item2, group.ToArray()))
            .OrderBy(scope => scope.Project, StringComparer.Ordinal).ThenBy(scope => scope.Scope, StringComparer.Ordinal).ToArray();
    }

    private static BoundTestScope Scope(string project, string name, ScribeBoundCallable[] roots)
    {
        var unknown = new HashSet<string>(StringComparer.Ordinal);
        var paths = new HashSet<string>(StringComparer.Ordinal);
        var edges = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Stack<ScribeBoundCallable>(roots);
        var visited = new HashSet<ScribeBoundCallable>();
        var type = roots[0].Symbol!.ContainingType;
        if (type.IsAbstract || type.IsGenericType || type.ContainingType is not null || type.BaseType?.SpecialType != SpecialType.System_Object
            || type.AllInterfaces.Length != 0)
            unknown.Add("test-lifecycle:inheritance-or-fixture");
        if (type.GetAttributes().Length != 0)
            unknown.Add("test-lifecycle:class-adapter-attribute");
        foreach (var root in roots)
        {
            if (root.Symbol!.IsAsync || root.Symbol.Parameters.Length != 0)
                unknown.Add("adapter:async-or-data-driven-test");
            foreach (var attribute in root.Symbol.GetAttributes())
                if (attribute.AttributeClass?.ToDisplayString() != "Xunit.FactAttribute" || attribute.NamedArguments.Length != 0)
                    unknown.Add("adapter:custom-or-configured-test-attribute");
        }
        while (pending.TryPop(out var callable))
        {
            if (!visited.Add(callable)) continue;
            var symbol = callable.Symbol!;
            var caller = symbol.ContainingAssembly.Name + ":" + symbol.GetDocumentationCommentId();
            foreach (var target in callable.Targets)
            {
                edges.Add(caller + " -> " + target.Symbol!.ContainingAssembly.Name + ":" + target.Symbol.GetDocumentationCommentId());
                pending.Push(target);
            }
            foreach (var reason in callable.BindingUnknownReasons) unknown.Add("binding:" + reason);
            // Initializers/dispatch which the Scribe graph does not promise to
            // traverse cannot be promoted to complete execution dependencies.
            if (symbol.IsVirtual || symbol.IsAbstract || symbol.IsExtern || symbol.ContainingType.TypeKind == TypeKind.Interface)
                unknown.Add("dispatch:" + caller);
            if (symbol.ContainingType.GetMembers().OfType<IFieldSymbol>().Any(field => !field.IsConst)
                || symbol.ContainingType.StaticConstructors.Length != 0
                || symbol.ContainingType.GetMembers().OfType<IMethodSymbol>().Any(method => method.MethodKind == MethodKind.Destructor)
                || symbol.ContainingType.BaseType is { SpecialType: not SpecialType.System_Object } && symbol.ContainingType.TypeKind == TypeKind.Class)
                unknown.Add("state-or-type-initializer:" + TypeName(symbol.ContainingType));
            foreach (var node in callable.InspectionNodes)
            {
                var model = callable.SemanticModel;
                if (node is InvocationExpressionSyntax && model.GetOperation(node) is INameOfOperation) continue;
                if (node is InvocationExpressionSyntax or ObjectCreationExpressionSyntax or ImplicitObjectCreationExpressionSyntax
                    or ConstructorInitializerSyntax or AttributeSyntax)
                {
                    var method = model.GetSymbolInfo(node).Symbol as IMethodSymbol;
                    if (method is null) { unknown.Add("unresolved-operation:" + callable.Path); continue; }
                    edges.Add(caller + " -> " + method.ContainingAssembly.Name + ":" + method.OriginalDefinition.GetDocumentationCommentId());
                    if (method.MethodKind == MethodKind.DelegateInvoke || method.IsVirtual || method.IsAbstract || method.IsExtern)
                        unknown.Add("dispatch:" + method.ToDisplayString());
                    if (callable.Targets.Any(target =>
                            target.Symbol!.ContainingAssembly.Name == method.ContainingAssembly.Name
                            && target.Symbol.GetDocumentationCommentId() == method.OriginalDefinition.GetDocumentationCommentId())) continue;
                    if (node is AttributeSyntax && method.ContainingType.ToDisplayString() == "Xunit.FactAttribute") continue;
                    if (ReadLiteral(method, node, model, paths))
                    { unknown.Add("runtime:io-host-context"); continue; }
                    if (!ScalarLeaf(method)) unknown.Add("external-call:" + method.ToDisplayString());
                }
                else if (node is MemberAccessExpressionSyntax or IdentifierNameSyntax or ElementAccessExpressionSyntax)
                {
                    if (node.Parent is InvocationExpressionSyntax) continue;
                    switch (model.GetSymbolInfo(node).Symbol)
                    {
                        case IPropertySymbol property when !property.Locations.Any(location => location.IsInSource):
                            unknown.Add("external-property:" + property.ToDisplayString()); break;
                        case IPropertySymbol property when !callable.Targets.Any(target =>
                            target.Symbol?.AssociatedSymbol?.GetDocumentationCommentId() == property.GetDocumentationCommentId()):
                            unknown.Add("unbound-property:" + property.ToDisplayString()); break;
                        case IFieldSymbol field when !field.IsConst && field.IsStatic:
                            unknown.Add("static-state:" + field.ToDisplayString()); break;
                    }
                }
                else if (node is AwaitExpressionSyntax or ForEachStatementSyntax or UsingStatementSyntax or LockStatementSyntax
                    or QueryExpressionSyntax or InterpolatedStringExpressionSyntax or AnonymousFunctionExpressionSyntax
                    or CollectionExpressionSyntax or InitializerExpressionSyntax or WithExpressionSyntax or PatternSyntax
                    or ForEachVariableStatementSyntax or RangeExpressionSyntax or TupleExpressionSyntax
                    or UnsafeStatementSyntax or FixedStatementSyntax or StackAllocArrayCreationExpressionSyntax
                    || node is LocalDeclarationStatementSyntax { UsingKeyword.RawKind: not 0 })
                    unknown.Add("implicit-runtime-operation:" + node.GetType().Name);
                if (node is ExpressionSyntax expression && model.GetTypeInfo(expression).Type?.TypeKind is TypeKind.Dynamic or TypeKind.Pointer or TypeKind.FunctionPointer)
                    unknown.Add("dynamic-or-native-dispatch");
                if (node is ExpressionSyntax converted && model.GetConversion(converted).MethodSymbol is not null)
                    unknown.Add("implicit-runtime-operation:user-conversion");
                if (model.GetOperation(node) is IBinaryOperation { OperatorMethod: not null }
                    or IUnaryOperation { OperatorMethod: not null } or IIncrementOrDecrementOperation { OperatorMethod: not null }
                    or ICompoundAssignmentOperation { OperatorMethod: not null })
                    unknown.Add("implicit-runtime-operation:user-operator");
            }
        }
        return new(project, name, roots.Select(root => name + "." + root.Name).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray(),
            paths.Order(StringComparer.Ordinal).ToArray(), edges.Order(StringComparer.Ordinal).ToArray(), unknown.Order(StringComparer.Ordinal).ToArray());
    }

    private static bool ReadLiteral(IMethodSymbol method, SyntaxNode node, SemanticModel model, HashSet<string> paths)
    {
        if (method.ContainingType.ToDisplayString() != "System.IO.File"
            || method.Name is not ("ReadAllText" or "ReadAllBytes" or "Exists")
            || node is not InvocationExpressionSyntax invocation || invocation.ArgumentList.Arguments.Count != 1
            || model.GetConstantValue(invocation.ArgumentList.Arguments[0].Expression) is not { HasValue: true, Value: string value }
            || string.IsNullOrEmpty(value)) return false;
        paths.Add(value);
        return true;
    }

    private static bool ScalarLeaf(IMethodSymbol method)
    {
        if (method.ContainingType.SpecialType == SpecialType.System_Object && method.MethodKind == MethodKind.Constructor) return true;
        if (method.ContainingAssembly.Name != "xunit.assert" || method.ContainingType.ToDisplayString() != "Xunit.Assert") return false;
        if (method.Name is "True" or "False" or "Null" or "NotNull" or "Same" or "NotSame") return true;
        // Equality over arbitrary objects can execute user comparers and cannot
        // be inferred from Assert's name. Only scalar value arguments close here.
        return method.Name == "Equal" && method.Parameters.All(parameter => Scalar(parameter.Type))
            && method.TypeArguments.All(Scalar);
    }

    private static bool Scalar(ITypeSymbol type) => type.SpecialType is SpecialType.System_Boolean
        or SpecialType.System_Char or SpecialType.System_SByte or SpecialType.System_Byte or SpecialType.System_Int16
        or SpecialType.System_UInt16 or SpecialType.System_Int32 or SpecialType.System_UInt32 or SpecialType.System_Int64
        or SpecialType.System_UInt64 or SpecialType.System_Decimal or SpecialType.System_Single or SpecialType.System_Double
        or SpecialType.System_String;
    private static string TypeName(INamedTypeSymbol type) => type.ToDisplayString();
}
