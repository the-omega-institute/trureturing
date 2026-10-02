using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace StrataLint.Scribe;

/// <summary>Unrecognized operations and unregistered external declarations are rejected.</summary>
internal sealed class ScribeScriptAdmission(CSharpCompilation compilation, ScribeScriptAllowlist allowlist)
{
    internal static ScribeScriptFailure? Validate(CSharpCompilation compilation,
        ImmutableArray<string> sources, ScribeScriptAllowlist allowlist)
    {
        var admission = new ScribeScriptAdmission(compilation, allowlist);
        var paths = sources.ToHashSet(StringComparer.Ordinal);
        foreach (var tree in compilation.SyntaxTrees.Where(tree => paths.Contains(tree.FilePath)))
        {
            var model = compilation.GetSemanticModel(tree);
            var nodes = tree.GetRoot().DescendantNodesAndSelf().ToArray();
            // Executable roots include methods, accessors, operators, initializers and nested functions.
            foreach (var node in nodes)
            {
                if (node is AttributeSyntax attribute)
                {
                    var failure = admission.Member(model.GetSymbolInfo(attribute).Symbol, node);
                    if (failure is not null) return failure;
                }
                var operation = model.GetOperation(node);
                if (operation is null || operation.Parent is not null) continue;
                foreach (var descendant in operation.DescendantsAndSelf())
                {
                    var failure = admission.Operation(descendant, model);
                    if (failure is not null) return failure;
                }
                foreach (var descendant in operation.DescendantsAndSelf())
                {
                    var failure = admission.Type(descendant.Type, descendant.Syntax);
                    if (failure is not null) return failure;
                }
            }
            foreach (var node in nodes)
            {
                var info = model.GetTypeInfo(node);
                var failure = admission.Type(info.Type, node) ?? admission.Type(info.ConvertedType, node);
                if (failure is not null) return failure;
            }
        }
        return null;
    }

    private ScribeScriptFailure? Operation(IOperation operation, SemanticModel model)
    {
        var node = operation.Syntax;
        ScribeScriptFailure? failure;
        switch (operation.Kind)
        {
            case OperationKind.Invocation:
                failure = Member(((IInvocationOperation)operation).TargetMethod, node); break;
            case OperationKind.ObjectCreation:
                failure = Member(((IObjectCreationOperation)operation).Constructor, node); break;
            case OperationKind.MethodReference:
                failure = Member(((IMethodReferenceOperation)operation).Method, node); break;
            case OperationKind.PropertyReference:
                failure = Member(((IPropertyReferenceOperation)operation).Property, node); break;
            case OperationKind.FieldReference:
                failure = Member(((IFieldReferenceOperation)operation).Field, node); break;
            case OperationKind.Binary:
                var binary = (IBinaryOperation)operation;
                failure = Member(binary.OperatorMethod, node);
                if (failure is null && binary.OperatorKind == BinaryOperatorKind.Add
                    && binary.Type?.SpecialType == SpecialType.System_String)
                    failure = Formatting(binary.LeftOperand) ?? Formatting(binary.RightOperand);
                break;
            case OperationKind.Unary:
                failure = Member(((IUnaryOperation)operation).OperatorMethod, node); break;
            case OperationKind.Increment:
            case OperationKind.Decrement:
                failure = Member(((IIncrementOrDecrementOperation)operation).OperatorMethod, node); break;
            case OperationKind.CompoundAssignment:
                var assignment = (ICompoundAssignmentOperation)operation;
                failure = Member(assignment.OperatorMethod, node)
                    ?? Member(assignment.InConversion.MethodSymbol, node)
                    ?? Member(assignment.OutConversion.MethodSymbol, node);
                if (failure is null && assignment.OperatorKind == BinaryOperatorKind.Add
                    && assignment.Type?.SpecialType == SpecialType.System_String)
                    failure = Formatting(assignment.Value);
                break;
            case OperationKind.Conversion:
                failure = Member(((IConversionOperation)operation).OperatorMethod, node); break;
            case OperationKind.Argument:
                var argument = (IArgumentOperation)operation;
                failure = Member(argument.InConversion.MethodSymbol, node)
                    ?? Member(argument.OutConversion.MethodSymbol, node); break;
            case OperationKind.ImplicitIndexerReference:
                var indexer = (IImplicitIndexerReferenceOperation)operation;
                failure = Member(indexer.LengthSymbol, node) ?? Member(indexer.IndexerSymbol, node); break;
            case OperationKind.Range:
                failure = Member(((IRangeOperation)operation).Method, node); break;
            case OperationKind.VariableDeclarator:
                failure = Type(((IVariableDeclaratorOperation)operation).Symbol.Type, node); break;
            case OperationKind.Interpolation:
                failure = Formatting(((IInterpolationOperation)operation).Expression); break;
            case OperationKind.Loop:
                failure = operation is IForEachLoopOperation loop ? Foreach(loop, model) : null; break;
            case OperationKind.CollectionExpression:
                failure = Collection((ICollectionExpressionOperation)operation, model); break;
            case OperationKind.Spread:
                var spread = (ISpreadOperation)operation;
                failure = Member(spread.ElementConversion.MethodSymbol, node)
                    ?? Enumeration(spread.Operand.Type, node, model); break;
            case OperationKind.Attribute:
            case OperationKind.AnonymousFunction:
            case OperationKind.ArrayCreation:
            case OperationKind.ArrayElementReference:
            case OperationKind.ArrayInitializer:
            case OperationKind.BinaryPattern:
            case OperationKind.Block:
            case OperationKind.Branch:
            case OperationKind.Coalesce:
            case OperationKind.Conditional:
            case OperationKind.ConstantPattern:
            case OperationKind.DeclarationExpression:
            case OperationKind.DeclarationPattern:
            case OperationKind.DefaultValue:
            case OperationKind.DelegateCreation:
            case OperationKind.Discard:
            case OperationKind.DiscardPattern:
            case OperationKind.ExpressionStatement:
            case OperationKind.FieldInitializer:
            case OperationKind.InstanceReference:
            case OperationKind.InterpolatedString:
            case OperationKind.InterpolatedStringText:
            case OperationKind.IsPattern:
            case OperationKind.Literal:
            case OperationKind.LocalFunction:
            case OperationKind.LocalReference:
            case OperationKind.MethodBodyOperation:
            case OperationKind.ConstructorBodyOperation:
            case OperationKind.NameOf:
            case OperationKind.NegatedPattern:
            case OperationKind.ObjectOrCollectionInitializer:
            case OperationKind.ParameterInitializer:
            case OperationKind.ParameterReference:
            case OperationKind.PropertyInitializer:
            case OperationKind.RelationalPattern:
            case OperationKind.Return:
            case OperationKind.SimpleAssignment:
            case OperationKind.SwitchExpression:
            case OperationKind.SwitchExpressionArm:
            case OperationKind.Throw:
            case OperationKind.Tuple:
            case OperationKind.VariableDeclaration:
            case OperationKind.VariableDeclarationGroup:
            case OperationKind.VariableInitializer:
                failure = null; break;
            default:
                return Disallowed(node, $"operation kind {operation.Kind}");
        }
        return failure;
    }

    private ScribeScriptFailure? Foreach(IForEachLoopOperation loop, SemanticModel model)
    {
        if (loop.IsAsynchronous) return Disallowed(loop.Syntax, "operation kind asynchronous Loop");
        if (loop.Syntax is not CommonForEachStatementSyntax syntax) return Disallowed(loop.Syntax, "unrecognized foreach");
        var info = model.GetForEachStatementInfo(syntax);
        return Member(info.GetEnumeratorMethod, syntax) ?? Member(info.MoveNextMethod, syntax)
            ?? Member(info.CurrentProperty, syntax) ?? Member(info.DisposeMethod, syntax)
            ?? Member(info.ElementConversion.MethodSymbol, syntax) ?? Member(info.CurrentConversion.MethodSymbol, syntax)
            ?? Type(info.ElementType, syntax);
    }

    private ScribeScriptFailure? Collection(ICollectionExpressionOperation collection, SemanticModel model)
    {
        var failure = Member(collection.ConstructMethod, collection.Syntax);
        if (failure is not null || collection.Type is IArrayTypeSymbol) return failure;
        if (collection.Type is not INamedTypeSymbol type) return Disallowed(collection.Syntax, "unrecognized collection type");
        if (collection.ConstructMethod is null && ScribeScriptAllowlist.Id(type) is
            "T:System.Collections.Generic.IEnumerable`1" or "T:System.Collections.Generic.IReadOnlyList`1"
            or "T:System.Collections.Generic.IReadOnlyCollection`1") return null;
        if (collection.ConstructMethod is { IsStatic: true }
            && ScribeScriptAllowlist.Id(type) == "T:System.Collections.Immutable.ImmutableArray`1") return null;
        if (ScribeScriptAllowlist.Id(type) != "T:System.Collections.Generic.List`1")
            return Disallowed(collection.Syntax, $"unrecognized collection construction {ScribeScriptAllowlist.Id(type)}");
        var add = model.LookupSymbols(collection.Syntax.SpanStart, type, "Add").OfType<IMethodSymbol>()
            .SingleOrDefault(method => method.Parameters.Length == 1 && SymbolEqualityComparer.Default.Equals(method.Parameters[0].Type, type.TypeArguments[0]));
        return add is null ? Disallowed(collection.Syntax, "unresolved collection Add") : Member(add, collection.Syntax);
    }

    private ScribeScriptFailure? Enumeration(ITypeSymbol? type, SyntaxNode node, SemanticModel model)
    {
        // Arrays and strings use intrinsic indexing. Other spreads require an explicit enumerable contract.
        if (type is IArrayTypeSymbol || type?.SpecialType == SpecialType.System_String) return null;
        if (type is not INamedTypeSymbol named) return Disallowed(node, "unrecognized spread enumeration");
        var enumerable = compilation.GetTypeByMetadataName("System.Collections.Generic.IEnumerable`1")!;
        var contract = named.AllInterfaces.Prepend(named).FirstOrDefault(candidate =>
            SymbolEqualityComparer.Default.Equals(candidate.OriginalDefinition, enumerable));
        if (contract is null) return Disallowed(node, $"unrecognized spread enumeration {ScribeScriptAllowlist.Id(named)}");
        // Pattern enumeration can override the interface contract; refuse it unless every selected member is registered.
        var candidates = model.LookupSymbols(node.SpanStart, named, "GetEnumerator").OfType<IMethodSymbol>()
            .Where(method => !method.IsStatic && method.Parameters.Length == 0
                && method.DeclaredAccessibility == Accessibility.Public).ToArray();
        var declared = candidates.Where(method => SymbolEqualityComparer.Default.Equals(method.ContainingType, named)).ToArray();
        if (declared.Length != 0) candidates = declared;
        if (named.TypeKind == TypeKind.Interface)
            candidates = candidates.Where(method => SymbolEqualityComparer.Default.Equals(
                method.ReturnType, contract.GetMembers("GetEnumerator").OfType<IMethodSymbol>().Single().ReturnType)).ToArray();
        if (candidates.Length > 1) return Disallowed(node, "ambiguous spread GetEnumerator");
        var get = candidates.SingleOrDefault() ?? contract.GetMembers("GetEnumerator").OfType<IMethodSymbol>().Single();
        var failure = Member(get, node);
        if (failure is not null) return failure;
        var enumerator = get.ReturnType;
        foreach (var name in new[] { "MoveNext", "Current", "Dispose" })
        {
            var symbols = enumerator.GetMembers(name);
            if (symbols.IsEmpty && enumerator is INamedTypeSymbol enumType)
                symbols = enumType.AllInterfaces.SelectMany(item => item.GetMembers(name)).ToImmutableArray();
            if (symbols.IsEmpty && name == "Dispose") continue;
            if (symbols.Length != 1) return Disallowed(node, $"unrecognized enumeration member {name}");
            failure = Member(symbols[0], node);
            if (failure is not null) return failure;
        }
        return null;
    }

    private ScribeScriptFailure? Formatting(IOperation value)
    {
        while (value is IConversionOperation { IsImplicit: true } conversion) value = conversion.Operand;
        if (value.Type is null && value.ConstantValue is { HasValue: true, Value: null }) return null;
        return value.Type is { } type && (IsScript(type) || allowlist.AllowsFormatting(type))
            ? null : Disallowed(value.Syntax, $"implicit formatting {TypeId(value.Type)}");
    }

    private ScribeScriptFailure? Member(ISymbol? symbol, SyntaxNode node)
    {
        if (symbol is null) return null;
        if (!IsScript(symbol) && !allowlist.AllowsMember(symbol))
            return Disallowed(node, ScribeScriptAllowlist.Id(symbol) ?? symbol.ToDisplayString());
        var failure = Type(symbol.ContainingType, node);
        if (failure is not null) return failure;
        switch (symbol)
        {
            case IMethodSymbol method:
                failure = Type(method.ReturnType, node);
                foreach (var argument in method.TypeArguments)
                    failure ??= Type(argument, node);
                return failure;
            case IPropertySymbol property: return Type(property.Type, node);
            case IFieldSymbol field: return Type(field.Type, node);
            default: return Disallowed(node, $"unrecognized member {symbol.Kind}");
        }
    }

    private ScribeScriptFailure? Type(ITypeSymbol? type, SyntaxNode node)
    {
        if (type is null || type is ITypeParameterSymbol) return null;
        if (type.TypeKind == TypeKind.Dynamic) return Disallowed(node, "T:System.Object (dynamic)");
        if (type is IPointerTypeSymbol or IFunctionPointerTypeSymbol) return Disallowed(node, "pointer type");
        if (type is IArrayTypeSymbol array)
            return Type(compilation.GetSpecialType(SpecialType.System_Array), node) ?? Type(array.ElementType, node);
        if (type is not INamedTypeSymbol named) return Disallowed(node, $"unrecognized type {type.TypeKind}");
        if (!IsScript(type) && !allowlist.AllowsType(type)) return Disallowed(node, TypeId(type));
        foreach (var argument in named.TypeArguments)
        {
            var failure = Type(argument, node);
            if (failure is not null) return failure;
        }
        return null;
    }

    private bool IsScript(ISymbol symbol) => SymbolEqualityComparer.Default.Equals(symbol.ContainingAssembly, compilation.Assembly);
    private static string TypeId(ITypeSymbol? type) => type is null ? "unresolved type" : ScribeScriptAllowlist.Id(type) ?? type.ToDisplayString();
    private static ScribeScriptFailure Disallowed(SyntaxNode node, string symbol)
    {
        var span = node.GetLocation().GetLineSpan();
        var path = span.Path.Replace('\\', '/');
        return new(ScribeScriptFailureCode.DisallowedSymbol, path,
            $"{path}:{span.StartLinePosition.Line + 1}: disallowed symbol {symbol}");
    }
}
