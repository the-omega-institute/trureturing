using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace StrataLint.Scribe;

/// <summary>Unrecognized operations and unregistered external declarations are rejected.</summary>
internal sealed class ScribeScriptAdmission(CSharpCompilation compilation, ScribeScriptAllowlist allowlist)
{
    private readonly ImmutableArray<INamedTypeSymbol> scriptTypes = ScriptTypes(compilation.Assembly.GlobalNamespace).ToImmutableArray();

    private static IEnumerable<INamedTypeSymbol> ScriptTypes(INamespaceOrTypeSymbol container)
    {
        foreach (var type in container.GetTypeMembers())
        {
            yield return type;
            foreach (var nested in ScriptTypes(type)) yield return nested;
        }
        if (container is INamespaceSymbol space)
            foreach (var child in space.GetNamespaceMembers())
                foreach (var type in ScriptTypes(child)) yield return type;
    }

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
                if (node is TypeDeclarationSyntax declaration
                    && model.GetDeclaredSymbol(declaration) is { } declared)
                {
                    var interfaceFailure = admission.DeclaredInterfaces(declaration, declared, model);
                    if (interfaceFailure is not null) return interfaceFailure;
                    foreach (var constructor in declared.InstanceConstructors.Where(method => !declared.IsValueType &&
                        method.IsImplicitlyDeclared && method.Parameters.IsEmpty))
                    {
                        var failure = admission.Member(constructor, node);
                        if (failure is not null) return failure;
                    }
                }
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

    private ScribeScriptFailure? DeclaredInterfaces(TypeDeclarationSyntax declaration,
        INamedTypeSymbol type, SemanticModel model)
    {
        if (type.TypeKind == TypeKind.Interface || declaration.BaseList is null) return null;
        var contracts = declaration.BaseList.Types
            .Select(item => model.GetTypeInfo(item.Type).Type).OfType<INamedTypeSymbol>()
            .Where(item => item.TypeKind == TypeKind.Interface)
            .SelectMany(item => item.AllInterfaces.Prepend(item)).Where(item => !IsScript(item))
            .Distinct<INamedTypeSymbol>(SymbolEqualityComparer.Default);
        foreach (var contract in contracts)
            foreach (var slot in contract.GetMembers().Where(member => member is IMethodSymbol { AssociatedSymbol: null }
                or IPropertySymbol or IEventSymbol))
            {
                var implementation = type.FindImplementationForInterfaceMember(slot);
                if (implementation is null)
                    return Disallowed(declaration, $"unresolved interface implementation {TypeId(type)} {ScribeScriptAllowlist.Id(slot)}");
                var failure = InspectImplementation(type, implementation, declaration)
                    ?? Dispatch(slot, declaration, type);
                if (failure is not null) return failure;
            }
        return null;
    }

    private ScribeScriptFailure? InspectImplementation(INamedTypeSymbol type, ISymbol implementation, SyntaxNode node)
    {
        if (implementation is IPropertySymbol property)
        {
            foreach (var accessor in new[] { property.GetMethod, property.SetMethod })
            {
                if (accessor is null) continue;
                var failure = InspectImplementation(type, accessor, node);
                if (failure is not null) return failure;
            }
            return InspectMember(property, node);
        }
        if (IsScript(implementation) && implementation is IMethodSymbol method
            && !method.DeclaringSyntaxReferences.Any(reference => reference.GetSyntax() switch
            {
                MethodDeclarationSyntax source => source.Body is not null || source.ExpressionBody is not null,
                AccessorDeclarationSyntax source => source.Body is not null || source.ExpressionBody is not null,
                PropertyDeclarationSyntax source => source.ExpressionBody is not null,
                IndexerDeclarationSyntax source => source.ExpressionBody is not null,
                ArrowExpressionClauseSyntax { Parent: PropertyDeclarationSyntax or IndexerDeclarationSyntax } => true,
                OperatorDeclarationSyntax source => source.Body is not null || source.ExpressionBody is not null,
                ConversionOperatorDeclarationSyntax source => source.Body is not null || source.ExpressionBody is not null,
                _ => false,
            }))
            return Disallowed(node, $"uninspected interface implementation {TypeId(type)} {ScribeScriptAllowlist.Id(method)}");
        var memberFailure = InspectMember(implementation, node);
        return memberFailure is null ? null : Disallowed(node,
            $"interface implementation {TypeId(type)} {ScribeScriptAllowlist.Id(implementation)}: {memberFailure.Message}");
    }

    private ScribeScriptFailure? Operation(IOperation operation, SemanticModel model)
    {
        var node = operation.Syntax;
        ScribeScriptFailure? failure;
        switch (operation.Kind)
        {
            case OperationKind.Invocation:
                var invocation = (IInvocationOperation)operation;
                failure = Member(invocation.TargetMethod, node, argumentsChecked: true, receiverType: invocation.Instance?.Type); break;
            case OperationKind.ObjectCreation:
                failure = Member(((IObjectCreationOperation)operation).Constructor, node, argumentsChecked: true); break;
            case OperationKind.MethodReference:
                var reference = (IMethodReferenceOperation)operation;
                failure = Member(reference.Method, node, receiverType: reference.Instance?.Type); break;
            case OperationKind.PropertyReference:
                var property = (IPropertyReferenceOperation)operation;
                failure = Member(property.Property, node, receiverType: property.Instance?.Type); break;
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
                    ?? Member(argument.OutConversion.MethodSymbol, node);
                if (failure is null && !allowlist.AllowsArgument(argument.Parameter, argument.Value))
                    failure = Disallowed(node, $"parameter {argument.Parameter!.Name} of {ScribeScriptAllowlist.Id(argument.Parameter.ContainingSymbol)} requires a registered constant");
                break;
            case OperationKind.ImplicitIndexerReference:
                var indexer = (IImplicitIndexerReferenceOperation)operation;
                failure = Member(indexer.LengthSymbol, node) ?? Member(indexer.IndexerSymbol, node); break;
            case OperationKind.Range:
                failure = Member(((IRangeOperation)operation).Method, node); break;
            case OperationKind.VariableDeclarator:
                failure = Type(((IVariableDeclaratorOperation)operation).Symbol.Type, node); break;
            case OperationKind.Interpolation:
                failure = Formatting(((IInterpolationOperation)operation).Expression, interpolation: true); break;
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

    private ScribeScriptFailure? Formatting(IOperation value, bool interpolation = false)
    {
        while (value is IConversionOperation { IsImplicit: true } conversion) value = conversion.Operand;
        if (value.Type is null && value.ConstantValue is { HasValue: true, Value: null }) return null;
        if (value.Type is not INamedTypeSymbol type) return Disallowed(value.Syntax, $"implicit formatting {TypeId(value.Type)}");
        if (!IsScript(type)) return allowlist.AllowsFormatting(type)
            ? null : Disallowed(value.Syntax, $"implicit formatting {TypeId(type)}");
        if (type.IsAbstract && type.TypeKind != TypeKind.Interface)
        {
            var failure = FormattingType(type, value.Syntax, interpolation);
            if (failure is not null) return failure;
        }
        foreach (var possible in scriptTypes.Append(type).Where(candidate => !candidate.IsAbstract
            && candidate.TypeKind != TypeKind.Interface && Related(candidate, type)).Distinct(SymbolEqualityComparer.Default))
        {
            var failure = FormattingType((INamedTypeSymbol)possible!, value.Syntax, interpolation);
            if (failure is not null) return failure;
        }
        return null;
    }

    private ScribeScriptFailure? FormattingType(INamedTypeSymbol type, SyntaxNode node, bool interpolation)
    {
        if (interpolation)
        {
            foreach (var metadataName in new[] { "System.ISpanFormattable", "System.IFormattable" })
            {
                var contract = compilation.GetTypeByMetadataName(metadataName);
                if (contract is null || !type.AllInterfaces.Contains(contract, SymbolEqualityComparer.Default)) continue;
                var method = contract.GetMembers().OfType<IMethodSymbol>().Single();
                var implementation = type.FindImplementationForInterfaceMember(method);
                if (implementation is null) return Disallowed(node, $"unresolved formatting {ScribeScriptAllowlist.Id(method)}");
                return Member(implementation, node, receiverType: type, dispatchSlot: method);
            }
        }
        // String concatenation and the fallback interpolation path dispatch Object.ToString virtually.
        for (INamedTypeSymbol? current = type; current is not null; current = current.BaseType)
        {
            var method = current.GetMembers("ToString").OfType<IMethodSymbol>().FirstOrDefault(candidate =>
                IsObjectToString(candidate));
            if (method is not null) return Member(method, node, receiverType: type);
        }
        return Disallowed(node, $"unresolved implicit formatting {TypeId(type)}");
    }

    private static bool IsObjectToString(IMethodSymbol method)
    {
        if (method.IsStatic || !method.Parameters.IsEmpty) return false;
        while (method.OverriddenMethod is { } overridden) method = overridden;
        return method.ContainingType.SpecialType == SpecialType.System_Object;
    }

    private ScribeScriptFailure? Member(ISymbol? symbol, SyntaxNode node, bool argumentsChecked = false,
        ITypeSymbol? receiverType = null, ISymbol? dispatchSlot = null)
    {
        if (symbol is null) return null;
        return Dispatch(dispatchSlot ?? symbol, node, receiverType) ?? InspectMember(symbol, node, argumentsChecked);
    }

    private ScribeScriptFailure? Dispatch(ISymbol symbol, SyntaxNode node, ITypeSymbol? receiverType)
    {
        if (symbol.IsStatic && !symbol.IsAbstract && !symbol.IsVirtual
            || symbol is not (IMethodSymbol or IPropertySymbol)
            || !(symbol.IsVirtual || symbol.IsAbstract || symbol.IsOverride
                || symbol.ContainingType.TypeKind == TypeKind.Interface)) return null;
        var receiver = receiverType ?? symbol.ContainingType;
        if (receiver is not INamedTypeSymbol named)
            return Disallowed(node, $"unresolved dispatch {ScribeScriptAllowlist.Id(symbol)}");
        var contract = symbol.ContainingType.TypeKind == TypeKind.Interface;
        if (!IsScript(named) && !IsScript(symbol) && !contract) return null;
        foreach (var type in scriptTypes.Where(type => type.TypeKind != TypeKind.Interface))
        {
            if (!Related(type, named)) continue;
            ISymbol?[] implementations;
            if (contract)
            {
                implementations = type.AllInterfaces.Prepend(type).Where(item => Same(item, symbol.ContainingType))
                    .Select(implemented =>
                    {
                        var member = implemented.GetMembers(symbol.Name).FirstOrDefault(item => Same(item, symbol));
                        var resolved = member is null ? null : type.FindImplementationForInterfaceMember(member);
                        return resolved is null ? null : VirtualImplementation(type, resolved);
                    }).ToArray();
            }
            else implementations = [VirtualImplementation(type, symbol)];
            if (implementations.Length == 0)
                return Disallowed(node, $"unresolved dispatch {TypeId(type)} {ScribeScriptAllowlist.Id(symbol)}");
            foreach (var implementation in implementations)
            {
                if (implementation is null || implementation.IsAbstract && !type.IsAbstract)
                    return Disallowed(node, $"unresolved dispatch {TypeId(type)} {ScribeScriptAllowlist.Id(symbol)}");
                if (contract && !IsScript(symbol))
                {
                    var interfaceFailure = InspectImplementation(type, implementation, node);
                    if (interfaceFailure is not null) return interfaceFailure;
                    continue;
                }
                var failure = InspectMember(implementation, node);
                if (failure is null && implementation is IPropertySymbol property)
                    foreach (var accessor in new[] { property.GetMethod, property.SetMethod })
                    {
                        if (accessor is null) continue;
                        failure ??= InspectMember(accessor, node);
                    }
                if (failure is not null) return failure;
            }
        }
        return null;
    }

    private static bool Related(INamedTypeSymbol type, INamedTypeSymbol receiver) =>
        receiver.TypeKind == TypeKind.Interface
            ? type.AllInterfaces.Any(item => Same(item, receiver))
            : Bases(type).Any(item => Same(item, receiver));

    private static IEnumerable<INamedTypeSymbol> Bases(INamedTypeSymbol type)
    {
        for (INamedTypeSymbol? current = type; current is not null; current = current.BaseType)
            yield return current;
    }

    private static bool Same(ISymbol left, ISymbol right) =>
        SymbolEqualityComparer.Default.Equals(left.OriginalDefinition, right.OriginalDefinition);

    private static ISymbol VirtualImplementation(INamedTypeSymbol type, ISymbol slot)
    {
        foreach (var current in Bases(type))
            foreach (var candidate in current.GetMembers(slot.Name))
                for (ISymbol? overridden = candidate; overridden is not null; overridden = overridden switch
                {
                    IMethodSymbol method => method.OverriddenMethod,
                    IPropertySymbol property => property.OverriddenProperty,
                    _ => null,
                })
                    if (Same(overridden, slot)) return candidate;
        return slot;
    }

    private ScribeScriptFailure? InspectMember(ISymbol? symbol, SyntaxNode node, bool argumentsChecked = false)
    {
        if (symbol is null) return null;
        if (!allowlist.AllowsTypeArguments(symbol))
            return Disallowed(node, $"unregistered type argument {ScribeScriptAllowlist.Id(symbol)}");
        if (!argumentsChecked && allowlist.HasParameterConstraints(symbol))
            return Disallowed(node, $"uncheckable parameter constraints {ScribeScriptAllowlist.Id(symbol)}");
        if (IsScript(symbol) && symbol is IMethodSymbol { IsImplicitlyDeclared: true } generated)
        {
            if (generated.MethodKind != MethodKind.Constructor || !generated.Parameters.IsEmpty)
                return Disallowed(node, $"uninspected generated member {ScribeScriptAllowlist.Id(generated)}");
            if (!generated.ContainingType.IsValueType && generated.ContainingType.BaseType is { } baseType)
            {
                var candidates = baseType.InstanceConstructors.Where(method => method.Parameters.IsEmpty).ToArray();
                if (candidates.Length == 0)
                    candidates = baseType.InstanceConstructors.Where(method =>
                        method.Parameters.All(parameter => parameter.IsOptional || parameter.IsParams)).ToArray();
                if (candidates.Length != 1)
                    return Disallowed(node, $"unrecognized implicit base constructor {ScribeScriptAllowlist.Id(baseType)}");
                var baseFailure = Member(candidates[0], node);
                if (baseFailure is not null) return baseFailure;
            }
        }
        if (!IsScript(symbol) && !allowlist.AllowsMember(symbol)
            && !(symbol is IMethodSymbol { AssociatedSymbol: IPropertySymbol registered } && allowlist.AllowsMember(registered)))
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
