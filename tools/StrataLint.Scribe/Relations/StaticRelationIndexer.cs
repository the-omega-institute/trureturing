using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public sealed record RelationReadFailure(string SourcePath, int Line, string Shape, string Detail);
public sealed record RelationReadResult(string RelativePath, RelationProjection? Projection, RelationReadFailure? Failure);

public static class StaticRelationIndexer
{
    public static RelationReadResult Read(string repositoryRoot, string relativePath) =>
        ReadPrepared(repositoryRoot, relativePath, ScribeScriptHost.ReferenceAssemblies());

    internal static RelationReadResult ReadPrepared(string repositoryRoot, string relativePath,
        ImmutableArray<MetadataReference> references)
    {
        var path = ScribeScriptHost.NormalizePath(relativePath);
        if (path is null) return Failure(relativePath, "InvalidPath", "Expected a normalized Blueprint definition path.");
        var options = ScribeScriptHost.ScriptParseOptions;
        if (options is null) return Failure(path, "HostConfiguration", "Script parse options are unavailable.");
        try
        {
            var graph = ScribeScriptHost.ReadSourceGraph(repositoryRoot, path, options);
            if (graph.Failure is { } failure) return Failure(path, failure.Code.ToString(), failure.Message);
            var compilation = ScribeScriptHost.CreateSourceCompilation(repositoryRoot, graph.Sources!.Value, references, options);
            return new(path, new RelationSyntaxEvaluator(compilation, path).Read(), null);
        }
        catch (RelationSyntaxException exception)
        {
            return new(path, null, exception.Failure);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or ArgumentException)
        {
            return Failure(path, "SourceRead", exception.Message);
        }
    }

    private static RelationReadResult Failure(string path, string shape, string detail) =>
        new(path, null, new(path, 1, shape, detail));
}

internal sealed class RelationSyntaxException(RelationReadFailure failure) : Exception(failure.Detail)
{
    internal RelationReadFailure Failure { get; } = failure;
}

/// <summary>A closed relation algebra; it never emits or invokes source-defined code.</summary>
internal sealed class RelationSyntaxEvaluator(Compilation compilation, string entry)
{
    internal const int MaximumHelperDepth = 8;
    private readonly HashSet<ISymbol> active = new(SymbolEqualityComparer.Default);
    private readonly HashSet<ISymbol> relationCarriers = new(SymbolEqualityComparer.Default);
    private readonly Dictionary<SyntaxTree, SemanticModel> models = [];
    private sealed record Binding(ExpressionSyntax Expression, Dictionary<ISymbol, object?> Scope);
    private sealed record InlineReference(string Target);
    private sealed record Claim(string Problem, string Resolution, ImmutableArray<string> Additional);
    private sealed record Header(string Gid, string? EvidenceReference, ImmutableArray<string> LiteratureAnchors);
    private sealed record Provenance(string? LiteratureReference, ImmutableArray<string> Acknowledgements);
    private sealed record Packet(Header Header, string Path, object? Content, object? Edges);

    private SemanticModel Model(SyntaxNode node)
    {
        if (!models.TryGetValue(node.SyntaxTree, out var model))
            models[node.SyntaxTree] = model = compilation.GetSemanticModel(node.SyntaxTree);
        return model;
    }

    internal RelationProjection Read()
    {
        var tree = compilation.SyntaxTrees.Single(tree => tree.FilePath == entry);
        var candidates = tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>()
            .Where(method => method.Identifier.ValueText == "Create"
                && Model(method).GetDeclaredSymbol(method)?.ReturnType.ToDisplayString() == "StrataLint.Scribe.DocumentDefinition")
            .Where(method => Model(method).GetDeclaredSymbol(method)?.ContainingType.AllInterfaces
                .Any(type => type.ToDisplayString() == "StrataLint.Scribe.IScribeDocumentDefinition") == true).ToArray();
        if (candidates.Length != 1) throw Reject(tree.GetRoot(), "DefinitionCount", $"Found {candidates.Length} entry methods.");
        relationCarriers.Clear();
        CollectRelationCarriers(candidates[0], new(SymbolEqualityComparer.Default));
        ValidatePresentationEffects(candidates[0], new(SymbolEqualityComparer.Default));
        var packet = Method(candidates[0], new(SymbolEqualityComparer.Default)) as Packet
            ?? throw Reject(candidates[0], "DocumentStructure", "Entry did not construct a document.");
        var content = Flatten(packet.Content).ToArray();
        return new(packet.Header.Gid, RelationProjection.NormalizeSource(packet.Path),
            Flatten(packet.Edges).OfType<RelationEdge>().ToImmutableArray(),
            content.OfType<InlineReference>().Select(static reference => reference.Target).ToImmutableArray(),
            content.OfType<RelationDescribe>().ToImmutableArray(),
            packet.Header.EvidenceReference, packet.Header.LiteratureAnchors);
    }

    private object? Method(SyntaxNode method, Dictionary<ISymbol, object?> scope)
    {
        var (expressionBody, body) = method switch
        {
            MethodDeclarationSyntax declaration => (declaration.ExpressionBody, declaration.Body),
            LocalFunctionStatementSyntax declaration => (declaration.ExpressionBody, declaration.Body),
            _ => throw Reject(method, "HelperBody", "Unsupported helper declaration."),
        };
        if (expressionBody is not null) return Eval(expressionBody.Expression, scope);
        if (body is null) throw Reject(method, "HelperBody", "Expected an expression or straight-line body.");
        foreach (var statement in body.Statements)
        {
            switch (statement)
            {
                case LocalDeclarationStatementSyntax local:
                    foreach (var variable in local.Declaration.Variables)
                    {
                        if (variable.Initializer is null) throw Reject(variable, "UninitializedLocal", "Local has no initializer.");
                        scope[Model(variable).GetDeclaredSymbol(variable)!] = new Binding(variable.Initializer.Value,
                            new(scope, SymbolEqualityComparer.Default));
                    }
                    break;
                case ReturnStatementSyntax { Expression: { } expression }:
                    return Eval(expression, scope);
                case LocalFunctionStatementSyntax:
                    break;
                default:
                    throw Reject(statement, statement.Kind().ToString(), "Only local initializers and one return are supported.");
            }
        }
        throw Reject(method, "MissingReturn", "Method has no return expression.");
    }

    private object? Eval(ExpressionSyntax expression, Dictionary<ISymbol, object?> scope)
    {
        // Control and indexing are refused even where Roslyn can fold a branch.
        if (expression is ConditionalExpressionSyntax or ElementAccessExpressionSyntax or LambdaExpressionSyntax)
            throw Reject(expression, expression.Kind().ToString(), "Unsupported relation expression.");
        var constant = Model(expression).GetConstantValue(expression);
        if (constant.HasValue && expression is LiteralExpressionSyntax or IdentifierNameSyntax or MemberAccessExpressionSyntax)
            return constant.Value;
        switch (expression)
        {
            case ParenthesizedExpressionSyntax parenthesized:
                return Eval(parenthesized.Expression, scope);
            case CastExpressionSyntax cast:
                var castValue = Eval(cast.Expression, scope);
                if (constant.HasValue) return constant.Value;
                var targetType = Model(cast).GetTypeInfo(cast.Type).Type;
                if (SymbolEqualityComparer.Default.Equals(targetType, Model(cast).GetTypeInfo(cast.Expression).Type)
                    || targetType?.SpecialType == SpecialType.System_String && castValue is string)
                    return castValue;
                throw Reject(cast, "UnsupportedCast", "Only constant, identity, and known string casts are supported.");
            case PostfixUnaryExpressionSyntax postfix when postfix.OperatorToken.ValueText == "!":
                return Eval(postfix.Operand, scope);
            case BinaryExpressionSyntax binary when binary.OperatorToken.ValueText == "+":
                if (Model(binary).GetTypeInfo(binary).Type?.SpecialType != SpecialType.System_String)
                    throw Reject(binary, "NonStringAddition", "Only string concatenation is supported.");
                return Component(binary.Left, scope) + Component(binary.Right, scope);
            case InterpolatedStringExpressionSyntax interpolated:
                return string.Concat(interpolated.Contents.Select(part => part switch
                {
                    InterpolatedStringTextSyntax text => text.TextToken.ValueText,
                    InterpolationSyntax interpolation when interpolation.AlignmentClause is null
                        && interpolation.FormatClause is null => Component(interpolation.Expression, scope),
                    _ => throw Reject(part, "InterpolationFormat", "Formatted interpolation is unsupported."),
                }));
            case CollectionExpressionSyntax collection:
                return collection.Elements.Select(element => element switch
                {
                    ExpressionElementSyntax item => Eval(item.Expression, scope),
                    SpreadElementSyntax spread => Eval(spread.Expression, scope),
                    _ => throw Reject(element, "CollectionElement", "Unknown collection element."),
                }).ToArray();
            case ArrayCreationExpressionSyntax { Initializer: { } initializer }:
                return initializer.Expressions.Select(item => Eval(item, scope)).ToArray();
            case ImplicitArrayCreationExpressionSyntax array:
                return array.Initializer.Expressions.Select(item => Eval(item, scope)).ToArray();
            case IdentifierNameSyntax or MemberAccessExpressionSyntax:
                return Symbol(expression, scope);
            case InvocationExpressionSyntax invocation:
                return Call(invocation, invocation.ArgumentList.Arguments, scope);
            case ObjectCreationExpressionSyntax creation:
                return Call(creation, creation.ArgumentList?.Arguments ?? default, scope);
            case ImplicitObjectCreationExpressionSyntax creation:
                return Call(creation, creation.ArgumentList.Arguments, scope);
            default:
                throw Reject(expression, expression.Kind().ToString(), "Unsupported relation expression.");
        }
    }

    private object? Symbol(ExpressionSyntax expression, Dictionary<ISymbol, object?> scope)
    {
        var symbol = Model(expression).GetSymbolInfo(expression).Symbol;
        if (expression is MemberAccessExpressionSyntax { Name.Identifier.ValueText: "Anchor" } anchorMember
            && symbol is IPropertySymbol anchorProperty
            && anchorProperty.ContainingType.ToDisplayString() == "StrataLint.Scribe.LibraryNoteRef")
            return LibraryNoteRef.Create(Scalar(Eval(anchorMember.Expression, scope), anchorMember)).Anchor;
        if (expression is MemberAccessExpressionSyntax { Name.Identifier.ValueText: "Value" } member
            && symbol is IPropertySymbol property && property.ContainingType.ToDisplayString() is
                "StrataLint.Scribe.GidRef" or "StrataLint.Scribe.DeclarationHandle"
                or "StrataLint.Scribe.LeanDeclarationRef" or "StrataLint.Scribe.DescribeId"
                or "StrataLint.Scribe.ProblemSlugRef" or "StrataLint.Scribe.LibraryNoteRef")
            return Eval(member.Expression, scope);
        if (symbol is not null && scope.TryGetValue(symbol, out var value))
            return ResolveBinding(value);
        if (symbol is IFieldSymbol { HasConstantValue: true } field) return field.ConstantValue;
        if (symbol is IParameterSymbol) throw Reject(expression, "UnboundParameter", "No constant helper argument.");
        if (symbol is IFieldSymbol sourceField && sourceField.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax()
            is VariableDeclaratorSyntax { Initializer.Value: { } initializer })
        {
            if (!sourceField.IsReadOnly) throw Reject(expression, "MutableField", "Only readonly field initializers are supported.");
            if (sourceField.ContainingType.Constructors.Any(constructor => !constructor.IsImplicitlyDeclared)
                || sourceField.ContainingType.StaticConstructors.Any(constructor => !constructor.IsImplicitlyDeclared))
                throw Reject(expression, "ConstructorState", "Explicit constructors may replace field initializers.");
            if (sourceField.Type is IArrayTypeSymbol)
                throw Reject(expression, "MutableField", "Readonly array contents may be mutated.");
            if (!active.Add(sourceField)) throw Reject(expression, "RecursiveHelper", "Recursive field initializer.");
            try { return Eval(initializer, scope); }
            finally { active.Remove(sourceField); }
        }
        throw Reject(expression, "UnresolvedSymbol", "Symbol has no supported static value.");
    }

    private object? ResolveBinding(object? value) => value is Binding binding ? Eval(binding.Expression, binding.Scope)
        : value is object?[] items ? items.Select(ResolveBinding).ToArray() : value;

    private void ValidatePresentationEffects(SyntaxNode node, HashSet<ISymbol> visited, bool ignored = false)
    {
        foreach (var child in node.DescendantNodes())
        {
            var childIgnored = ignored || child.Ancestors().Any(IsIgnoredPresentationCall);
            if (child is AssignmentExpressionSyntax assignment)
            {
                if (IsRelationWrite(assignment.Left, childIgnored))
                    throw Reject(assignment, "IgnoredWrite", "Ignored source code may not write observable state.");
            }
            if (child is PrefixUnaryExpressionSyntax { OperatorToken.ValueText: "++" or "--" } prefix)
            {
                if (IsRelationWrite(prefix.Operand, childIgnored))
                    throw Reject(prefix, "IgnoredWrite", "Ignored source code may not write observable state.");
            }
            if (child is PostfixUnaryExpressionSyntax { OperatorToken.ValueText: "++" or "--" } postfix)
            {
                if (IsRelationWrite(postfix.Operand, childIgnored))
                    throw Reject(postfix, "IgnoredWrite", "Ignored source code may not write observable state.");
            }
            if (child is ArgumentSyntax argument && argument.RefKindKeyword.RawKind != 0)
                throw Reject(argument, "IgnoredWrite", "By-reference source arguments may mutate observable state.");
            if (child is InvocationExpressionSyntax invocation
                && Model(invocation).GetSymbolInfo(invocation).Symbol is IMethodSymbol method)
            {
                if (childIgnored && !IsRecognizedInvocation(method))
                    throw Reject(invocation, "IgnoredWrite", "Ignored source code may call only recognized pure operations.");
                if (method.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is { } helper
                    && helper is MethodDeclarationSyntax or LocalFunctionStatementSyntax
                    && visited.Add(method))
                    ValidatePresentationEffects(helper, visited, childIgnored);
                if (method.ContainingType.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.List<T>"
                    && method.Name is "Add" or "AddRange" or "Clear" or "Remove" or "RemoveAt"
                    && method.ContainingType.TypeArguments.Any(IsRelationType))
                    throw Reject(invocation, "IgnoredWrite", "Source code may mutate a relation collection.");
            }
        }
    }

    private bool IsRelationWrite(ExpressionSyntax target, bool ignored)
    {
        var type = Model(target).GetTypeInfo(target).Type;
        if (type is null) return false;
        var symbol = Model(target).GetSymbolInfo(target).Symbol;
        if (ignored) return true;
        if (symbol is ILocalSymbol or IParameterSymbol)
            return relationCarriers.Contains(symbol) || IsRelationType(type) && type.SpecialType != SpecialType.System_String;
        return IsRelationType(type);
    }

    private void CollectRelationCarriers(SyntaxNode node, HashSet<ISymbol> visited)
    {
        foreach (var invocation in node.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            var method = Model(invocation).GetSymbolInfo(invocation).Symbol as IMethodSymbol;
            if (method is null) continue;
            if (method.ContainingType.ToDisplayString() == "StrataLint.Scribe.DefinitionDsl" && method.Name is "Ref")
            {
                foreach (var identifier in invocation.ArgumentList.Arguments.SelectMany(argument =>
                    argument.Expression.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()))
                {
                    if (Model(identifier).GetSymbolInfo(identifier).Symbol is { } symbol)
                        relationCarriers.Add(symbol);
                }
            }
            if (method.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is { } helper
                && helper is MethodDeclarationSyntax or LocalFunctionStatementSyntax
                && visited.Add(method))
                CollectRelationCarriers(helper, visited);
        }
    }

    private bool IsRecognizedInvocation(IMethodSymbol method)
    {
        if (method.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is MethodDeclarationSyntax or LocalFunctionStatementSyntax)
            return true;
        var type = method.ContainingType.ToDisplayString();
        if (method.ContainingType.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.List<T>"
            && method.Name is "Add" or "AddRange")
            return !method.ContainingType.TypeArguments.Any(IsRelationType);
        if (type == "System.Linq.Enumerable"
            && method.Name is "Select" or "SelectMany" or "Where" or "Concat" or "Append" or "ToArray"
                or "Aggregate" or "Reverse")
            return true;
        if (type == "System.Array" && method.Name == "ConvertAll") return true;
        if (type is "string" or "System.String" && method.Name is "Split") return true;
        return type is "string" or "System.String" && method.Name is "ToLowerInvariant" or "ToUpperInvariant" or "Trim" or "Replace"
            || type.StartsWith("StrataLint.Scribe.", StringComparison.Ordinal);
    }

    private bool IsIgnoredPresentationCall(SyntaxNode node) => node switch
    {
        InvocationExpressionSyntax invocation when Model(invocation).GetSymbolInfo(invocation).Symbol is IMethodSymbol method =>
            IsIgnoredPresentationMethod(method),
        ObjectCreationExpressionSyntax creation when Model(creation).GetSymbolInfo(creation).Symbol is IMethodSymbol method =>
            IsIgnoredPresentationMethod(method),
        ImplicitObjectCreationExpressionSyntax creation when Model(creation).GetSymbolInfo(creation).Symbol is IMethodSymbol method =>
            IsIgnoredPresentationMethod(method),
        _ => false,
    };

    private static bool IsIgnoredPresentationMethod(IMethodSymbol method) =>
        (method.ContainingType.ToDisplayString(), method.Name) switch
        {
            ("StrataLint.Scribe.DefinitionDsl", "Text" or "Math") => true,
            ("StrataLint.Scribe.Inline.Text" or "StrataLint.Scribe.Inline.InlineFormula", ".ctor") => true,
            ("StrataLint.Scribe.DocumentBlock.DisplayFormula", ".ctor") => true,
            _ => false,
        };

    private static bool IsRelationType(ITypeSymbol type) => type.SpecialType == SpecialType.System_String
        || type.ToDisplayString().StartsWith("StrataLint.Scribe.DocumentBlock", StringComparison.Ordinal)
        || type.ToDisplayString().StartsWith("StrataLint.Scribe.DocumentEdge", StringComparison.Ordinal)
        || type.ToDisplayString().StartsWith("StrataLint.Scribe.Inline", StringComparison.Ordinal)
        || type.ToDisplayString() is "StrataLint.Scribe.GidRef" or "StrataLint.Scribe.DeclarationHandle"
            or "StrataLint.Scribe.LeanDeclarationRef" or "StrataLint.Scribe.DescribeId"
            or "StrataLint.Scribe.ProblemSlugRef" or "StrataLint.Scribe.LibraryNoteRef"
            or "StrataLint.Scribe.BlockSequence" or "StrataLint.Scribe.OpenProblemResolutionClaim"
            or "StrataLint.Scribe.ScribeDocument" or "StrataLint.Scribe.DocumentDefinition"
            or "StrataLint.Scribe.DocumentHeader"
        || type.ToDisplayString().StartsWith("StrataLint.Scribe.AssessedProvenance", StringComparison.Ordinal)
        || type.ToDisplayString().StartsWith("StrataLint.Scribe.EvidenceMirror", StringComparison.Ordinal)
        || type.ToDisplayString() is "StrataLint.Engine.Anchor" or "StrataLint.Engine.LiteratureAnchor";

    private object? Call(ExpressionSyntax node, SeparatedSyntaxList<ArgumentSyntax> arguments,
        Dictionary<ISymbol, object?> scope)
    {
        if (node is InvocationExpressionSyntax { Expression: IdentifierNameSyntax { Identifier.ValueText: "nameof" } })
            throw Reject(node, "UnsupportedInvocation", "nameof is outside the closed relation expression set.");
        var symbol = Model(node).GetSymbolInfo(node).Symbol as IMethodSymbol
            ?? throw Reject(node, "UnresolvedInvocation", "No method symbol.");
        var type = symbol.ContainingType.ToDisplayString();
        var name = symbol.Name;
        var mapped = Arguments(symbol, arguments, scope, node);
        object? Arg(string parameter) => mapped.TryGetValue(parameter, out var value)
            ? Resolve(value) : null;
        string Str(string parameter) => Scalar(Arg(parameter), node);
        object? Resolve(object? value) => value is Binding binding ? Eval(binding.Expression, binding.Scope)
            : value is object?[] items ? items.Select(Resolve).ToArray() : value;

        if (type == "string" || type == "System.String")
        {
            if (node is not InvocationExpressionSyntax { Expression: MemberAccessExpressionSyntax member })
                throw Reject(node, "UnsupportedInvocation", "Unsupported string invocation.");
            if (name is not ("ToLowerInvariant" or "ToUpperInvariant" or "Trim" or "Replace"))
                throw Reject(node, "UnsupportedInvocation", "String operation is outside the closed set.");
            var receiver = Scalar(Eval(member.Expression, scope), member);
            return name switch
            {
                "ToLowerInvariant" when arguments.Count == 0 => receiver.ToLowerInvariant(),
                "ToUpperInvariant" when arguments.Count == 0 => receiver.ToUpperInvariant(),
                "Trim" when arguments.Count == 0 => receiver.Trim(),
                "Replace" when Arg("oldValue") is string oldValue && Arg("newValue") is string newValue =>
                    receiver.Replace(oldValue, newValue, StringComparison.Ordinal),
                "Replace" when Arg("oldChar") is char oldChar && Arg("newChar") is char newChar =>
                    receiver.Replace(oldChar, newChar),
                _ => throw Reject(node, "UnsupportedInvocation", "String operation is outside the closed set."),
            };
        }
        if (symbol.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is { } helper
            && helper is MethodDeclarationSyntax or LocalFunctionStatementSyntax)
        {
            if (!symbol.IsStatic) throw Reject(node, "InstanceHelper", "Only static helpers may be expanded.");
            if (!active.Add(symbol)) throw Reject(node, "RecursiveHelper", "Recursive helper call.");
            if (active.Count > MaximumHelperDepth) throw Reject(node, "HelperDepth", "Helper expansion depth exceeded.");
            try
            {
                var nested = new Dictionary<ISymbol, object?>(SymbolEqualityComparer.Default);
                foreach (var parameter in symbol.Parameters)
                    nested[parameter] = mapped.GetValueOrDefault(parameter.Name);
                return Method(helper, nested);
            }
            finally { active.Remove(symbol); }
        }
        if (type == "StrataLint.Engine.Anchor" && name == "ParseCanonical")
            return Anchor.TryParseCanonical(Str("value")) is AnchorParseResult.Parsed parsedAnchor
                ? parsedAnchor.Value
                : throw Reject(node, "InvalidAnchor", "Anchor factory argument is not canonical.");
        if (!type.StartsWith("StrataLint.Scribe.", StringComparison.Ordinal))
            throw Reject(node, "UnsupportedInvocation", $"Unsupported factory: {type}.{name}");
        switch (type, name)
        {
            case ("StrataLint.Scribe.DocumentDefinition", "Create"):
                var packet = Arg("document") as Packet
                    ?? throw Reject(node, "DocumentStructure", "Document argument is unsupported.");
                return packet with { Path = Str("sourcePath") };
            case ("StrataLint.Scribe.ScribeNode", "Create"):
                var path = RelationProjection.NormalizeSource(Str("sourcePath"));
                if (!path.StartsWith("Blueprint/", StringComparison.Ordinal) || !path.EndsWith(".scribe.cs", StringComparison.Ordinal))
                    throw Reject(node, "InvalidDocumentPath", "Document source path is outside Blueprint.");
                return new Packet(new Header(path["Blueprint/".Length..^".scribe.cs".Length], null, Anchors(Arg("anchors"))),
                    path, Arg("content"), Arg("edges"));
            case ("StrataLint.Scribe.ScribeDocument", "Create"):
                return new Packet(Arg("header") as Header
                    ?? throw Reject(node, "DocumentStructure", "Header argument is unsupported."), entry, Arg("content"), Arg("edges"));
            case ("StrataLint.Scribe.DefinitionDsl", "Header"):
                return new Header(Str("gid"), null, Anchors(Arg("anchors")));
            case ("StrataLint.Scribe.DocumentHeader", "Create"):
                return new Header(Str("gid"), Arg("mirrorEvidence") as string, Anchors(Arg("anchors")));
            case ("StrataLint.Scribe.EvidenceMirror.Artifact", ".ctor"):
                return Str("Reference");
            case ("StrataLint.Scribe.EvidenceMirror.Waiver", ".ctor"):
                return null;
            case ("StrataLint.Scribe.DefinitionDsl", "Blocks"):
            case ("StrataLint.Scribe.DefinitionDsl", "Paragraph"):
                return Arg("content");
            case ("StrataLint.Scribe.BlockSequence", "Create"):
            case ("StrataLint.Scribe.InlineSequence", "Create"):
                return Arg("items");
            case ("StrataLint.Scribe.DocumentBlock.Section", ".ctor"):
                return Arg("Content");
            case ("StrataLint.Scribe.DocumentBlock.Paragraph", ".ctor"):
                return Arg("Content");
            case ("StrataLint.Scribe.DefinitionDsl", "Ref"):
                return new InlineReference(Str("value"));
            case ("StrataLint.Scribe.Inline.GidReference", ".ctor"):
                return new InlineReference(Str("Reference"));
            case ("StrataLint.Scribe.DefinitionDsl", "Text" or "Math"):
            case ("StrataLint.Scribe.Inline.Text" or "StrataLint.Scribe.Inline.InlineFormula", ".ctor"):
            case ("StrataLint.Scribe.DocumentBlock.DisplayFormula", ".ctor"):
                return Array.Empty<object>();
            case ("StrataLint.Scribe.GidRef" or "StrataLint.Scribe.DeclarationHandle"
                or "StrataLint.Scribe.LeanDeclarationRef" or "StrataLint.Scribe.DescribeId"
                or "StrataLint.Scribe.ProblemSlugRef" or "StrataLint.Scribe.LibraryNoteRef", "Create"):
                return Str("value");
            case ("StrataLint.Scribe.DocumentEdge.Dependency", "Create"):
                return new RelationEdge("dependency", "document", Str("target"), null);
            case ("StrataLint.Scribe.DocumentEdge.TruthAnchor", "Create"):
                return new RelationEdge("truth", "declaration", Str("target"), null);
            case ("StrataLint.Scribe.DocumentEdge.NarrativeReference", "ToDocument"):
                return new RelationEdge("narrative", "document", Str("target"), null);
            case ("StrataLint.Scribe.DocumentEdge.NarrativeReference", "ToDescribe"):
                return new RelationEdge("narrative", "describe", Str("document"), Str("describe"));
            case ("StrataLint.Scribe.OpenProblemResolutionClaim", ".ctor"):
                return new Claim(Str("problemSlug"), EnumName(symbol.Parameters[1].Type, Arg("resolutionKind"), node),
                    Flatten(Arg("additionalMembers")).Select(value => Scalar(value, node)).ToImmutableArray());
            case ("StrataLint.Scribe.AssessedProvenance", "FromRepo" or "NovelAfterSearch"):
                return new Provenance(null, Flatten(Arg("acknowledgements")).Select(value => Scalar(value, node)).ToImmutableArray());
            case ("StrataLint.Scribe.AssessedProvenance", "FromLiterature"):
                return new Provenance(Str("noteRef"), []);
            case ("StrataLint.Scribe.Describe", "Lean" or "Remark" or "Example"):
                var declaration = Arg("handle") as string;
                var reportDerived = declaration is not null;
                var role = name == "Remark" && reportDerived ? "Remark"
                    : Arg("role") is { } authoredRole ? EnumName(compilation.GetTypeByMetadataName("StrataLint.Scribe.DescribeRole")!, authoredRole, node) : null;
                var claim = Arg("openProblemResolutionClaim") as Claim;
                var provenance = Arg("provenance") as Provenance
                    ?? throw Reject(node, "DescribeProvenance", "Provenance argument is unsupported.");
                var describe = new RelationDescribe(Str("id"), reportDerived ? "report-derived" : "authored",
                    reportDerived ? role : name, role, declaration,
                    claim is null ? null : new(claim.Problem, claim.Resolution,
                        new[] { declaration ?? string.Empty }.Concat(claim.Additional).Order(StringComparer.Ordinal).ToImmutableArray()),
                    provenance.LiteratureReference, provenance.Acknowledgements);
                return new object?[] { describe, Arg("narrative") };
            default:
                throw Reject(node, "UnsupportedInvocation", $"Unsupported relation factory: {type}.{name}");
        }
    }

    private static ImmutableArray<string> Anchors(object? value) => Flatten(value).OfType<LiteratureAnchor>()
        .Select(static anchor => anchor.CanonicalString).ToImmutableArray();

    private Dictionary<string, object?> Arguments(IMethodSymbol method, SeparatedSyntaxList<ArgumentSyntax> arguments,
        Dictionary<ISymbol, object?> scope, SyntaxNode node)
    {
        var result = new Dictionary<string, object?>(StringComparer.Ordinal);
        var operationArguments = Model(node).GetOperation(node) switch
        {
            IInvocationOperation invocation => invocation.Arguments,
            IObjectCreationOperation creation => creation.Arguments,
            _ => ImmutableArray<IArgumentOperation>.Empty,
        };
        for (var index = 0; index < arguments.Count; index++)
        {
            var argument = arguments[index];
            var parameter = index < operationArguments.Length
                ? operationArguments[index].Parameter
                : argument.NameColon is { } named
                    ? method.Parameters.First(parameter => parameter.Name == named.Name.Identifier.ValueText)
                    : method.Parameters[Math.Min(index, method.Parameters.Length - 1)];
            parameter ??= method.Parameters[Math.Min(index, method.Parameters.Length - 1)];
            var binding = new Binding(argument.Expression, scope);
            if (parameter.IsParams)
            {
                var existing = result.GetValueOrDefault(parameter.Name) as object?[] ?? [];
                result[parameter.Name] = existing.Append(binding).ToArray();
            }
            else result[parameter.Name] = binding;
        }
        foreach (var parameter in method.Parameters.Where(parameter => !result.ContainsKey(parameter.Name)))
        {
            result[parameter.Name] = parameter.GetAttributes().Any(attribute => attribute.AttributeClass?.ToDisplayString()
                == "System.Runtime.CompilerServices.CallerFilePathAttribute") ? node.SyntaxTree.FilePath
                : parameter.HasExplicitDefaultValue ? parameter.ExplicitDefaultValue : null;
        }
        return result;
    }

    private static string Scalar(object? value, SyntaxNode node) => value switch
    {
        string text => text,
        char character => character.ToString(),
        IFormattable number when value is byte or sbyte or short or ushort or int or uint or long or ulong =>
            number.ToString(null, System.Globalization.CultureInfo.InvariantCulture),
        _ => throw Reject(node, "NonConstantString", "Expected a constant string component."),
    };

    private string Component(ExpressionSyntax expression, Dictionary<ISymbol, object?> scope)
    {
        if (Model(expression).GetTypeInfo(expression).Type?.TypeKind == TypeKind.Enum)
            throw Reject(expression, "NonConstantString", "Enum formatting is outside the closed string component set.");
        return Scalar(Eval(expression, scope), expression);
    }

    private static string EnumName(ITypeSymbol type, object? value, SyntaxNode node) =>
        type.GetMembers().OfType<IFieldSymbol>().FirstOrDefault(field => field.HasConstantValue
            && Equals(field.ConstantValue, value))?.Name
        ?? throw Reject(node, "EnumValue", "Unknown enum value.");

    private static IEnumerable<object> Flatten(object? value)
    {
        if (value is object?[] items)
        {
            foreach (var item in items)
                foreach (var nested in Flatten(item)) yield return nested;
        }
        else if (value is not null) yield return value;
    }

    private static RelationSyntaxException Reject(SyntaxNode node, string shape, string detail) =>
        new(new(node.SyntaxTree.FilePath, node.GetLocation().GetLineSpan().StartLinePosition.Line + 1, shape, detail));
}
