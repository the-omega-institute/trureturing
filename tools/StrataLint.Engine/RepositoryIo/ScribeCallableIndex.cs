using Microsoft.CodeAnalysis;

namespace StrataLint.Engine;

internal readonly record struct ScribeCallableIdentity(string AssemblyName, string DeclarationId);

internal sealed class ScribeSemanticModelProvider
{
    private readonly Dictionary<SyntaxTree, Compilation> compilationByTree = new(
        ReferenceEqualityComparer.Instance);

    internal void Add(Compilation compilation)
    {
        foreach (var tree in compilation.SyntaxTrees) compilationByTree.TryAdd(tree, compilation);
    }

    internal SemanticModel? ModelFor(SyntaxNode node, SemanticModel fallback) =>
        ReferenceEquals(node.SyntaxTree, fallback.SyntaxTree)
            ? fallback
            : compilationByTree.TryGetValue(node.SyntaxTree, out var compilation)
                ? compilation.GetSemanticModel(node.SyntaxTree)
                : null;
}

internal sealed class ScribeCallableIndex
{
    private readonly Dictionary<IMethodSymbol, ScribeBoundCallable> bySymbol = new(
        SymbolEqualityComparer.Default);
    private readonly Dictionary<ScribeCallableIdentity, ScribeBoundCallable> byIdentity = [];

    internal bool Contains(IMethodSymbol method) => bySymbol.ContainsKey(Normalize(method));

    internal void Add(IMethodSymbol method, ScribeBoundCallable callable)
    {
        var normalized = Normalize(method);
        bySymbol.Add(normalized, callable);
        if (Identity(normalized) is { } identity) byIdentity.TryAdd(identity, callable);
    }

    internal bool TryGetValue(IMethodSymbol method, out ScribeBoundCallable callable)
    {
        var normalized = Normalize(method);
        if (bySymbol.TryGetValue(normalized, out callable!)) return true;
        return Identity(normalized) is { } identity
            && byIdentity.TryGetValue(identity, out callable!);
    }

    internal static IMethodSymbol Normalize(IMethodSymbol method) =>
        (method.ReducedFrom ?? method).OriginalDefinition;

    private static ScribeCallableIdentity? Identity(IMethodSymbol method)
    {
        var declarationId = DocumentationCommentId.CreateDeclarationId(method);
        return declarationId is null
            ? null
            : new ScribeCallableIdentity(method.ContainingAssembly.Identity.Name, declarationId);
    }
}
