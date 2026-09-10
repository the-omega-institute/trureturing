using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace StrataLint.Engine;

internal sealed record BoundTestScope(string Project, string[] Methods, string[] Rows,
    string[] RuntimeInputs, string[] Providers, string[] Unknown, int Callables);

// ExplicitValues is a reviewed declared-input contract, not a CLR purity proof.
// Native inputs own code invalidation. This single project-union pass binds the
// ordinary xUnit roots and local providers, and rejects known ambient effects.
// Scribe's SL003 mapping and debt do not participate in this contract.
internal static class ScribeExecutionDependencies
{
    internal static BoundTestScope Derive(ScribeProjectCompilationContext context, string project,
        Func<string, string[], object?[], string> formatRow)
    {
        var built = ScribeProjectCompilationBuilder.Build([], context);
        var compilations = built.ToDictionary(p => p.Compilation.AssemblyName!, p => p.Compilation, StringComparer.Ordinal);
        var models = built.SelectMany(p => p.Compilation.SyntaxTrees.Select(tree => (tree, model: p.Compilation.GetSemanticModel(tree))))
            .ToDictionary(p => p.tree, p => p.model);
        var test = built.Single(p => p.ProjectPath == project).Compilation;
        var unknown = new SortedSet<string>(StringComparer.Ordinal);
        var methods = new SortedSet<string>(StringComparer.Ordinal);
        var rows = new List<string>();
        var providers = new SortedSet<string>(StringComparer.Ordinal);
        var paths = new SortedSet<string>(StringComparer.Ordinal);
        var pending = new Queue<ISymbol>();
        var visited = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        var initialized = new HashSet<string>(StringComparer.Ordinal);
        var inspected = new HashSet<SyntaxNode>();
        foreach (var compilation in compilations.Values)
        {
            if (compilation.GetDiagnostics().Any(d => d.Severity == DiagnosticSeverity.Error))
                unknown.Add("compiler:semantic-errors:" + compilation.AssemblyName);
            foreach (var attribute in compilation.Assembly.GetAttributes())
                if (IsLifecycle(attribute.AttributeClass)) unknown.Add("test-lifecycle:assembly-adapter-attribute");
            foreach (var tree in compilation.SyntaxTrees)
            foreach (var declaration in tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>())
            {
                var method = models[tree].GetDeclaredSymbol(declaration)!;
                if (method.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() == "System.Runtime.CompilerServices.ModuleInitializerAttribute"))
                    unknown.Add("runtime:module-initializer:" + method.ToDisplayString());
                if (compilation != test || !method.GetAttributes().Any(a => IsTest(a.AttributeClass))) continue;
                var name = method.ContainingType.ToDisplayString() + "." + method.Name;
                methods.Add(name);
                var type = method.ContainingType;
                if (type.IsAbstract || type.IsGenericType || type.ContainingType is not null
                    || type.BaseType?.SpecialType != SpecialType.System_Object || type.AllInterfaces.Length != 0
                    || type.GetAttributes().Length != 0)
                    unknown.Add("test-lifecycle:inheritance-or-fixture:" + name);
                if (type.InstanceConstructors.Any(ctor => ctor.Parameters.Length != 0 || ctor.DeclaredAccessibility != Accessibility.Public))
                    unknown.Add("test-lifecycle:constructor-provider:" + name);
                if (method.IsAsync || method.IsStatic || method.IsGenericMethod || !method.ReturnsVoid
                    || method.DeclaredAccessibility != Accessibility.Public)
                    unknown.Add("adapter:unsupported-root:" + name);
                var attributes = method.GetAttributes();
                if (attributes.Any(a => a.NamedArguments.Length != 0 || a.AttributeClass?.ToDisplayString()
                    is not ("Xunit.FactAttribute" or "Xunit.TheoryAttribute" or "Xunit.InlineDataAttribute")))
                    unknown.Add("adapter:custom-or-configured-test-attribute:" + name);
                if (attributes.Any(a => a.AttributeClass?.ToDisplayString() == "Xunit.TheoryAttribute"))
                {
                    var data = attributes.Where(a => a.AttributeClass?.ToDisplayString() == "Xunit.InlineDataAttribute").ToArray();
                    if (data.Length == 0) unknown.Add("adapter:unresolved-data-provider:" + name);
                    foreach (var row in data)
                    {
                        var values = row.ConstructorArguments is [{ Kind: TypedConstantKind.Array } argument]
                            && !argument.IsNull ? argument.Values.ToArray() : [];
                        if (values.Length != method.Parameters.Length || values.Any(v => v.Kind is not (TypedConstantKind.Primitive or TypedConstantKind.Enum)
                                || v.Kind == TypedConstantKind.Enum))
                        { unknown.Add("adapter:unsupported-inline-values:" + name); continue; }
                        rows.Add(formatRow(name, method.Parameters.Select(p => p.Name).ToArray(), values.Select(v => v.Value).ToArray()));
                    }
                }
                else if (method.Parameters.Length == 0 && attributes.Any(a => a.AttributeClass?.ToDisplayString() == "Xunit.FactAttribute")) rows.Add(name);
                else unknown.Add("adapter:unsupported-fact:" + name);
                pending.Enqueue(method);
                Initialize(type, instance: true);
                foreach (var ctor in type.InstanceConstructors) pending.Enqueue(ctor);
            }
        }
        if (methods.Count == 0) unknown.Add("adapter:no-bound-test-identities");
        while (pending.TryDequeue(out var symbol))
        {
            symbol = Resolve(symbol);
            if (!visited.Add(symbol)) continue;
            var id = symbol.ContainingAssembly.Name + ":" + symbol.GetDocumentationCommentId();
            providers.Add(id);
            if (symbol is IMethodSymbol { IsExtern: true } or IMethodSymbol { IsAbstract: true }
                || symbol.ContainingType?.TypeKind == TypeKind.Interface)
                unknown.Add("dispatch:" + id);
            if (symbol.ContainingType is { } type) Initialize(type, symbol is IMethodSymbol { MethodKind: MethodKind.Constructor });
            if (symbol.DeclaringSyntaxReferences.Length == 0 && !symbol.IsImplicitlyDeclared)
                unknown.Add("binding:unresolved-native-member:" + id);
            foreach (var reference in symbol.DeclaringSyntaxReferences)
            {
                var declaration = reference.GetSyntax();
                // Compiler-synthesized record members are ordinary value semantics.
                // Only their initializers/default values are inspected, not every method.
                if (declaration is TypeDeclarationSyntax) continue;
                Inspect(declaration);
            }
        }
        return new(project, methods.ToArray(), rows.Order(StringComparer.Ordinal).ToArray(), paths.ToArray(),
            providers.ToArray(), unknown.ToArray(), visited.Count);

        ISymbol Resolve(ISymbol symbol)
        {
            if (symbol is IMethodSymbol method) symbol = ScribeCallableIndex.Normalize(method);
            else symbol = symbol.OriginalDefinition;
            return symbol.GetDocumentationCommentId() is { } id && compilations.TryGetValue(symbol.ContainingAssembly.Name, out var owner)
                ? DocumentationCommentId.GetFirstSymbolForDeclarationId(id, owner) ?? symbol : symbol;
        }
        void Initialize(INamedTypeSymbol input, bool instance)
        {
            var type = (INamedTypeSymbol)Resolve(input);
            if (!compilations.ContainsKey(type.ContainingAssembly.Name)) return;
            var key = type.ContainingAssembly.Name + ":" + type.GetDocumentationCommentId() + ":" + instance;
            if (!initialized.Add(key)) return;
            if (type.GetAttributes().Length != 0) unknown.Add("binding:custom-value-metadata:" + key);
            foreach (var ctor in type.StaticConstructors) pending.Enqueue(ctor);
            if (instance)
                foreach (var member in type.AllInterfaces.SelectMany(contract => contract.GetMembers()))
                    if (type.FindImplementationForInterfaceMember(member) is { } implementation) Enqueue(implementation);
            foreach (var member in type.GetMembers())
            {
                if (member is IMethodSymbol { MethodKind: MethodKind.Destructor }) unknown.Add("test-lifecycle:finalizer:" + key);
                // Pinned value consumers (serialization/assertion formatting) can
                // read getters implicitly. Bind constructed values' properties.
                if (instance && member is IPropertySymbol) pending.Enqueue(member);
                if (instance && member is IPropertySymbol or IFieldSymbol && member.GetAttributes().Length != 0)
                    unknown.Add("binding:custom-value-member-metadata:" + member.ToDisplayString());
                if (instance && member is IMethodSymbol m && (m.IsOverride || m.ExplicitInterfaceImplementations.Length != 0)) pending.Enqueue(m);
                if (member is not (IFieldSymbol or IPropertySymbol) || !instance && !member.IsStatic) continue;
                foreach (var syntax in member.DeclaringSyntaxReferences.Select(r => r.GetSyntax()))
                {
                    if (syntax is VariableDeclaratorSyntax { Initializer: { } field }) Inspect(field.Value);
                    if (syntax is PropertyDeclarationSyntax { Initializer: { } property }) Inspect(property.Value);
                }
            }
            if (instance && type.BaseType is { SpecialType: not SpecialType.System_Object } parent)
            {
                Initialize(parent, true);
                foreach (var ctor in parent.InstanceConstructors) Enqueue(ctor);
            }
        }
        void Enqueue(ISymbol symbol)
        {
            if (symbol is INamedTypeSymbol type) { Initialize(type, false); return; }
            if (symbol.ContainingAssembly is null) return;
            if (compilations.ContainsKey(symbol.ContainingAssembly.Name))
            {
                if (symbol is IMethodSymbol { MethodKind: MethodKind.DelegateInvoke }) return;
                pending.Enqueue(symbol); return;
            }
            if (Ambient(symbol)) unknown.Add("runtime:ambient-input:" + symbol.ToDisplayString());
            else if (!Platform(symbol.ContainingAssembly)) unknown.Add("binding:unresolved-provider:" + symbol.ToDisplayString());
        }
        void Inspect(SyntaxNode declaration)
        {
            if (!models.TryGetValue(declaration.SyntaxTree, out var model))
            { unknown.Add("binding:unresolved-source:" + declaration.SyntaxTree.FilePath); return; }
            foreach (var node in declaration.DescendantNodesAndSelf())
            {
                if (!inspected.Add(node) || node.AncestorsAndSelf().Any(n => n is AttributeSyntax)) continue;
                if (node is AnonymousFunctionExpressionSyntax or LocalFunctionStatementSyntax)
                    providers.Add("callback:" + declaration.SyntaxTree.FilePath + ":" + node.SpanStart);
                if (node is ExpressionSyntax expression)
                {
                    if (model.GetTypeInfo(expression).Type?.TypeKind is TypeKind.Dynamic or TypeKind.Pointer or TypeKind.FunctionPointer)
                        unknown.Add("dynamic-or-native-dispatch:" + declaration.SyntaxTree.FilePath);
                    if (model.GetConversion(expression).MethodSymbol is { } conversion) Enqueue(conversion);
                }
                if (node is InvocationExpressionSyntax or BaseObjectCreationExpressionSyntax or ConstructorInitializerSyntax)
                {
                    if (model.GetOperation(node) is INameOfOperation) continue;
                    if (model.GetSymbolInfo(node).Symbol is not IMethodSymbol call)
                    { unknown.Add("binding:unresolved-call:" + declaration.SyntaxTree.FilePath); continue; }
                    if (call.MethodKind != MethodKind.DelegateInvoke) Enqueue(call);
                    if (node is BaseObjectCreationExpressionSyntax) Initialize(call.ContainingType, true);
                    if (node is InvocationExpressionSyntax invocation && Ambient(call))
                        foreach (var argument in invocation.ArgumentList.Arguments)
                            if (model.GetConstantValue(argument.Expression) is { HasValue: true, Value: string value }
                                && call.ContainingNamespace.ToDisplayString().StartsWith("System.IO", StringComparison.Ordinal)) paths.Add(value);
                }
                else if (node is MemberAccessExpressionSyntax or IdentifierNameSyntax or ElementAccessExpressionSyntax)
                {
                    if (model.GetSymbolInfo(node).Symbol is IPropertySymbol or IFieldSymbol or IMethodSymbol)
                        Enqueue(model.GetSymbolInfo(node).Symbol!);
                }
                if (model.GetOperation(node) is IBinaryOperation { OperatorMethod: { } binary }) Enqueue(binary);
                if (model.GetOperation(node) is IUnaryOperation { OperatorMethod: { } unary }) Enqueue(unary);
                if (node is ForEachStatementSyntax loop)
                {
                    var info = model.GetForEachStatementInfo(loop);
                    foreach (var member in new ISymbol?[] { info.GetEnumeratorMethod, info.MoveNextMethod, info.CurrentProperty, info.DisposeMethod })
                        if (member is not null) Enqueue(member);
                }
            }
        }
    }

    private static bool IsTest(INamedTypeSymbol? type) => type is not null
        && (type.ToDisplayString() is "Xunit.FactAttribute" or "Xunit.TheoryAttribute" || IsTest(type.BaseType));
    private static bool IsLifecycle(INamedTypeSymbol? type) => type is not null
        && (type.ToDisplayString().StartsWith("Xunit.", StringComparison.Ordinal)
            || type.AllInterfaces.Any(i => i.ToDisplayString().StartsWith("Xunit.", StringComparison.Ordinal)) || IsLifecycle(type.BaseType));
    private static bool Platform(IAssemblySymbol assembly) =>
        assembly.Name is "xunit.core" or "xunit.assert" or "xunit.abstractions"
        || Convert.ToHexStringLower(assembly.Identity.PublicKeyToken.AsSpan()) is
            "b03f5f7f11d50a3a" or "7cec85d7bea7798e" or "b77a5c561934e089" or "cc7b13ffcd2ddd51";

    // Known capability boundaries, not a growing whitelist of pure BCL methods.
    private static bool Ambient(ISymbol symbol)
    {
        var type = symbol.ContainingType?.ToDisplayString() ?? "";
        var ns = symbol.ContainingNamespace?.ToDisplayString() ?? "";
        return type is "System.Environment" or "System.Random" or "System.TimeProvider"
            or "System.Diagnostics.Process" or "System.Diagnostics.ProcessStartInfo" or "System.Diagnostics.Stopwatch"
            or "System.IO.File" or "System.IO.Directory" or "System.IO.FileInfo" or "System.IO.DirectoryInfo"
            or "System.IO.FileSystemInfo" or "System.IO.FileStream" or "System.IO.StreamReader" or "System.IO.StreamWriter" or "System.IO.DriveInfo"
            || ns.StartsWith("System.Net", StringComparison.Ordinal) || ns.StartsWith("System.Reflection", StringComparison.Ordinal)
            || ns.StartsWith("System.Threading", StringComparison.Ordinal) || ns.StartsWith("System.Runtime.Loader", StringComparison.Ordinal)
            || type is "System.IO.FileSystemWatcher" or "System.Security.Cryptography.RandomNumberGenerator"
            || ns.StartsWith("System.Runtime.InteropServices", StringComparison.Ordinal)
            || type is "System.DateTime" or "System.DateTimeOffset" && symbol.Name is "Now" or "UtcNow" or "Today"
            || type == "System.Guid" && symbol.Name == "NewGuid"
            || type == "System.IO.Path" && symbol.Name is "GetFullPath" or "GetTempPath" or "GetTempFileName" or "GetRandomFileName"
            || type == "System.Threading.Thread" && symbol.Name is not ("get_CurrentCulture" or "get_CurrentUICulture");
    }
}
