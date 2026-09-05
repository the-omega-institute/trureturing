using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using System.Collections.Concurrent;
using System.Security.Cryptography;
using System.Text;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal static partial class ScriptTestInputDeriver
{
    // 判官须指名这几个测试脚手架类型,但 Engine 在依赖偏序的下方、引用不到测试程序集,
    // 故只能以名字指代。**按 metadata type name 而非全限定名匹配**:脚手架的 namespace
    // 迁移时,判据不应随之失效。仓库根 provider 还须由方法符号证明其程序集 owner,
    // 并证明是 static、parameterless、string-returning FindRoot。
    //
    // 案由(第 20″ 条):PR #5324 把 TestRepositoryLayout / RepositoryRelativePath
    // 迁入 StrataLint.TestSupport,此处 6 处硬编码的 "StrataLint.Tests.*" 未同步,
    // 而 ScribeTestSymbolBinder.IsRepositoryRootExpression 按方法名 FindRoot 判定、
    // 与 namespace 无关 ⟹ 两个判官对同一表达式分歧:
    // 「认得出是仓库根、却解析不出路径」→ AddResolved 的 default 分支 fail-closed throw
    // ⟹ dev 由绿转红(run 33910501229),经 #5331 撤因。
    // 字符串常量指向类型时编译器不红,故 #5324 自身三门全绿。
    //
    // 悬空由 ScriptTestGateClosureTests.JudgeNamedHelperTypesResolveToDeclaredTypes
    // 以 typeof(...) 钉住:这些类型被改名或删除即**编译期**红;仓库根 helper 的程序集
    // 移动也会使具名断言红,不会静默改变 owner identity。
    internal const string RepositoryLayoutAssemblyName = "StrataLint.TestSupport";
    // 程序集名是**有意**的 pin(不是漏改的全限定名):它把「谁是仓库根提供者」限定到
    // 唯一那个脚手架程序集,使别处同名的 look-alike 类型无法冒充 —— 反面由
    // ScriptTestGateClosureTests 的 StrataLint.Lookalike 夹具钉住。故脚手架换程序集时
    // 本常量必须跟着改,而 typeof(...) 断言保证「忘了改」在编译期即红。
    internal const string RepositoryLayoutTypeName = "TestRepositoryLayout";
    internal const string RepositoryRelativePathTypeName = "RepositoryRelativePath";
    internal const string ScriptHarnessScratchTypeName = "ScriptHarnessScratch";
    internal const string ProcessRunnerTypeName = "TestProcessRunner";

    private static void AddResolved(
        ExpressionSyntax? expression,
        ScribeBoundCallable callable,
        string identity,
        IDictionary<string, string> inputs)
    {
        if (expression is null
            || ScribePathProvenance.IsNonRepository(
                expression,
                callable.SemanticModel,
                callable.SemanticModels))
        {
            return;
        }

        var value = ResolvePath(
            expression,
            callable.SemanticModel,
            callable.SemanticModels,
            new HashSet<ISymbol>(SymbolEqualityComparer.Default));
        switch (value.Kind)
        {
            case PathValueKind.NonRepository:
            case PathValueKind.RepositoryRoot:
                return;
            case PathValueKind.RepositoryPath:
                if (IsGeneratedControllerOperand(value.Value!))
                    return;
                inputs.TryAdd(value.Value!, identity);
                return;
            default:
                if (ScribeTestSymbolBinder.IsRepositoryRootExpression(
                        expression,
                        callable.SemanticModel))
                {
                    throw Failure(identity, "unresolved repository-rooted path expression");
                }
                return;
        }
    }

    private static PathValue ResolvePath(
        ExpressionSyntax expression,
        SemanticModel fallback,
        ScribeSemanticModelProvider models,
        HashSet<ISymbol> visited)
    {
        var model = models.ModelFor(expression, fallback) ?? fallback;
        if (ScribePathProvenance.IsNonRepository(expression, model, models))
            return PathValue.NonRepository;
        if (model.GetConstantValue(expression) is { HasValue: true, Value: string constant })
            return new PathValue(PathValueKind.Literal, constant);
        if (expression is InterpolatedStringExpressionSyntax interpolated)
            return ResolveInterpolated(interpolated, model, models, visited);

        if (expression is InvocationExpressionSyntax invocation
            && BoundMethod(invocation, model) is { } method)
        {
            var owner = method.ContainingType.ToDisplayString();
            if (IsRepositoryRootProvider(method))
                return PathValue.RepositoryRoot;
            if (owner == "System.IO.Path" && method.Name == "Combine")
                return ResolveCombine(invocation, model, models, visited);
            if (owner == "System.IO.Path" && method.Name is "GetFullPath" or "GetDirectoryName")
                return invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression is { } argument
                    ? ResolvePath(argument, model, models, visited)
                    : PathValue.Unknown;
            if (method.ContainingType.Name == RepositoryRelativePathTypeName && method.Name == "Create")
            {
                var relative = invocation.ArgumentList.Arguments.SingleOrDefault()?.Expression;
                return relative is not null
                    && model.GetConstantValue(relative) is { HasValue: true, Value: string path }
                        ? new PathValue(PathValueKind.RepositoryPath, NormalizeRelative(path))
                        : PathValue.Unknown;
            }
            if (method.Locations.Any(static location => location.IsInSource))
                return ResolveReturns(method, model, models, visited);
        }

        var symbol = model.GetSymbolInfo(expression).Symbol;
        if (symbol is not ILocalSymbol and not IFieldSymbol and not IPropertySymbol
            || !visited.Add(symbol))
        {
            return PathValue.Unknown;
        }
        try
        {
            var values = Initializers(symbol).ToArray();
            if (values.Length == 0) return PathValue.Unknown;
            return Merge(values.Select(value => ResolvePath(value, model, models, visited)));
        }
        finally
        {
            visited.Remove(symbol);
        }
    }

    private static PathValue ResolveCombine(
        InvocationExpressionSyntax invocation,
        SemanticModel model,
        ScribeSemanticModelProvider models,
        HashSet<ISymbol> visited)
    {
        var arguments = invocation.ArgumentList.Arguments;
        if (arguments.Count < 2) return PathValue.Unknown;
        var current = ResolvePath(arguments[0].Expression, model, models, visited);
        if (current.Kind is not (PathValueKind.Literal or PathValueKind.RepositoryRoot
            or PathValueKind.RepositoryPath or PathValueKind.NonRepository))
        {
            return PathValue.Unknown;
        }
        for (var index = 1; index < arguments.Count; index++)
        {
            if (model.GetConstantValue(arguments[index].Expression) is not
                { HasValue: true, Value: string segment })
            {
                return current.Kind == PathValueKind.NonRepository
                    ? PathValue.NonRepository
                    : PathValue.Unknown;
            }
            if (current.Kind != PathValueKind.NonRepository)
            {
                var prefix = current.Kind == PathValueKind.RepositoryRoot ? string.Empty : current.Value!;
                current = new PathValue(
                    current.Kind == PathValueKind.Literal
                        ? PathValueKind.Literal
                        : PathValueKind.RepositoryPath,
                    current.Kind == PathValueKind.Literal
                        ? prefix.Length == 0 ? segment : prefix + "/" + segment
                        : NormalizeRelative(prefix.Length == 0 ? segment : prefix + "/" + segment));
            }
        }
        return current;
    }

    private static PathValue ResolveInterpolated(
        InterpolatedStringExpressionSyntax interpolated,
        SemanticModel model,
        ScribeSemanticModelProvider models,
        HashSet<ISymbol> visited)
    {
        var current = new PathValue(PathValueKind.Literal, string.Empty);
        foreach (var content in interpolated.Contents)
        {
            if (content is InterpolationSyntax interpolation)
            {
                if (current.Kind != PathValueKind.Literal || current.Value!.Length != 0)
                    return PathValue.Unknown;
                current = ResolvePath(interpolation.Expression, model, models, visited);
                continue;
            }

            if (content is not InterpolatedStringTextSyntax text)
                return PathValue.Unknown;
            var segment = text.TextToken.ValueText;
            current = current.Kind switch
            {
                PathValueKind.Literal => current with { Value = current.Value + segment },
                PathValueKind.RepositoryRoot => new PathValue(
                    PathValueKind.RepositoryPath,
                    NormalizeRelative(segment)),
                PathValueKind.RepositoryPath => new PathValue(
                    PathValueKind.RepositoryPath,
                    NormalizeRelative(current.Value + "/" + segment)),
                PathValueKind.NonRepository => PathValue.NonRepository,
                _ => PathValue.Unknown,
            };
        }
        return current;
    }

    private static PathValue ResolveReturns(
        IMethodSymbol method,
        SemanticModel model,
        ScribeSemanticModelProvider models,
        HashSet<ISymbol> visited)
    {
        method = ScribeCallableIndex.Normalize(method);
        if (!visited.Add(method)) return PathValue.Unknown;
        try
        {
            var values = method.DeclaringSyntaxReferences
                .Select(static reference => reference.GetSyntax())
                .SelectMany(ReturnValues)
                .ToArray();
            return values.Length == 0
                ? PathValue.Unknown
                : Merge(values.Select(value => ResolvePath(value, model, models, visited)));
        }
        finally
        {
            visited.Remove(method);
        }
    }

    private static IEnumerable<ExpressionSyntax> Initializers(ISymbol symbol) =>
        symbol.DeclaringSyntaxReferences
            .Select(static reference => reference.GetSyntax())
            .SelectMany(static syntax => syntax switch
            {
                VariableDeclaratorSyntax { Initializer.Value: { } value } => [value],
                PropertyDeclarationSyntax { Initializer.Value: { } value } => [value],
                PropertyDeclarationSyntax { ExpressionBody.Expression: { } value } => [value],
                _ => Array.Empty<ExpressionSyntax>(),
            });

    private static IEnumerable<ExpressionSyntax> ReturnValues(SyntaxNode declaration)
    {
        var expression = declaration switch
        {
            MethodDeclarationSyntax method => method.ExpressionBody?.Expression,
            LocalFunctionStatementSyntax local => local.ExpressionBody?.Expression,
            AccessorDeclarationSyntax accessor => accessor.ExpressionBody?.Expression,
            _ => null,
        };
        if (expression is not null) yield return expression;
        foreach (var statement in declaration.DescendantNodes(static node =>
                     node is not LocalFunctionStatementSyntax
                         and not AnonymousFunctionExpressionSyntax
                         and not TypeDeclarationSyntax)
                 .OfType<ReturnStatementSyntax>())
        {
            if (statement.Expression is not null) yield return statement.Expression;
        }
    }

    private static PathValue Merge(IEnumerable<PathValue> values)
    {
        var distinct = values.Distinct().ToArray();
        return distinct.Length == 1 ? distinct[0] : PathValue.Unknown;
    }

    private static IMethodSymbol? BoundMethod(InvocationExpressionSyntax invocation, SemanticModel model) =>
        model.GetSymbolInfo(invocation).Symbol as IMethodSymbol
        ?? (model.GetOperation(invocation) as Microsoft.CodeAnalysis.Operations.IInvocationOperation)?.TargetMethod;

    private static bool IsRepositoryRootProvider(IMethodSymbol method) =>
        method.ContainingAssembly.Name == RepositoryLayoutAssemblyName
        && method.ContainingType.MetadataName == RepositoryLayoutTypeName
        && method.Name == "FindRoot"
        && method.IsStatic
        && method.Parameters.Length == 0
        && method.ReturnType.SpecialType == SpecialType.System_String;

    private static bool IsPathBearing(ExpressionSyntax expression, SemanticModel model)
    {
        var type = model.GetTypeInfo(expression).ConvertedType ?? model.GetTypeInfo(expression).Type;
        if (type?.SpecialType == SpecialType.System_String) return true;
        if (type is IArrayTypeSymbol { ElementType.SpecialType: SpecialType.System_String }) return true;
        return type?.AllInterfaces.Any(static candidate =>
            candidate.OriginalDefinition.SpecialType == SpecialType.System_Collections_Generic_IEnumerable_T
            && candidate.TypeArguments is [{ SpecialType: SpecialType.System_String }]) == true;
    }

    private static bool IsDirectoryEnumeration(IMethodSymbol? method) =>
        method?.ContainingType.ToDisplayString() == "System.IO.Directory"
        && method.Name is "EnumerateFiles" or "GetFiles" or "EnumerateDirectories"
            or "GetDirectories" or "EnumerateFileSystemEntries" or "GetFileSystemEntries";

    private static bool IsPathTransformation(IMethodSymbol? method) =>
        method?.ContainingType.ToDisplayString() == "System.IO.Path"
        && method.Name is "Combine" or "GetFullPath" or "GetDirectoryName" or "GetRelativePath";

    private static bool IsConsumingInvocation(
        InvocationExpressionSyntax invocation,
        IMethodSymbol? method,
        int? parameterOrdinal,
        SemanticModel model)
    {
        if (method is null) return false;
        var owner = method.ContainingType.ToDisplayString();
        return method.ContainingType.Name == ScriptHarnessScratchTypeName
                && method.Name == "CopyScriptInto" && parameterOrdinal == 0
            || method.ContainingType.Name == ProcessRunnerTypeName
                && method.Name == "Run" && parameterOrdinal is 0 or 1
            || IsProcessStartInfoArgumentListAdd(invocation, method, model)
                && parameterOrdinal == 0
            || method.ContainingType.Name == RepositoryLayoutTypeName
                && method.Name == "ReadAllText" && parameterOrdinal == 0
            || owner == "System.IO.File"
                && method.Name is "ReadAllText" or "ReadAllBytes" or "ReadAllLines"
                && parameterOrdinal == 0
            || owner == "System.IO.File" && method.Name == "Copy" && parameterOrdinal == 0;
    }

    private static bool IsTestProcessRunner(IMethodSymbol? method) =>
        method?.ContainingType.Name == ProcessRunnerTypeName
        && method.Name == "Run";

    private static IEnumerable<ExpressionSyntax> StringCollectionOperands(
        ExpressionSyntax expression,
        SemanticModel model)
    {
        if ((model.GetTypeInfo(expression).ConvertedType ?? model.GetTypeInfo(expression).Type)?
            .SpecialType == SpecialType.System_String)
        {
            yield return expression;
            yield break;
        }

        IEnumerable<ExpressionSyntax>? elements = expression switch
        {
            CollectionExpressionSyntax collection => collection.Elements.SelectMany(static element => element switch
            {
                ExpressionElementSyntax item => new[] { item.Expression },
                SpreadElementSyntax spread => new[] { spread.Expression },
                _ => Array.Empty<ExpressionSyntax>(),
            }),
            ImplicitArrayCreationExpressionSyntax { Initializer: { } initializer } => initializer.Expressions,
            ArrayCreationExpressionSyntax { Initializer: { } initializer } => initializer.Expressions,
            InitializerExpressionSyntax initializer => initializer.Expressions,
            _ => null,
        };
        if (elements is not null)
        {
            foreach (var element in elements)
            foreach (var operand in StringCollectionOperands(element, model))
                yield return operand;
            yield break;
        }

        if (ScribeTestSymbolBinder.IsRepositoryRootExpression(expression, model))
            yield return expression;
    }

    private static bool IsProcessStartInfoArgumentListAdd(
        InvocationExpressionSyntax invocation,
        IMethodSymbol? method,
        SemanticModel model) =>
        method?.Name == "Add"
        && invocation.Expression is MemberAccessExpressionSyntax { Expression: var receiver }
        && model.GetSymbolInfo(receiver).Symbol is IPropertySymbol property
        && IsProcessStartInfoProperty(property, "ArgumentList");

    private static bool IsProcessStartInfoProperty(IPropertySymbol property, params string[] names) =>
        property.ContainingType.ToDisplayString() == "System.Diagnostics.ProcessStartInfo"
        && names.Contains(property.Name, StringComparer.Ordinal);

    private static bool IsGeneratedControllerOperand(string path) =>
        path.Contains("/bin/", StringComparison.Ordinal)
        && path.EndsWith("/StrataLint.EngineeringScope.dll", StringComparison.Ordinal);

    private static string NormalizeRelative(string path) =>
        string.Join('/', path.Replace('\\', '/').Split('/', StringSplitOptions.RemoveEmptyEntries));

    private static InvalidDataException Failure(string identity, string reason) =>
        new($"ScriptTests gate {identity}: {reason}");

    private enum PathValueKind { Unknown, Literal, NonRepository, RepositoryRoot, RepositoryPath }

    private readonly record struct PathValue(PathValueKind Kind, string? Value = null)
    {
        internal static PathValue Unknown => new(PathValueKind.Unknown);
        internal static PathValue NonRepository => new(PathValueKind.NonRepository);
        internal static PathValue RepositoryRoot => new(PathValueKind.RepositoryRoot);
    }

    private readonly record struct OperationUse(IOperation? Consumer, int? ParameterOrdinal);

    private sealed class RepositoryValueWalker(
        ScribeBoundCallable callable,
        string identity,
        IDictionary<string, string> inputs) : OperationWalker
    {
        private readonly HashSet<IOperation> visited = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<(SyntaxTree Tree, int Start, int Length)> inspectedValues = [];

        public override void Visit(IOperation? operation)
        {
            if (operation is null || !visited.Add(operation)) return;
            base.Visit(operation);
            if (operation.Syntax is ExpressionSyntax expression
                && inspectedValues.Add((expression.SyntaxTree, expression.SpanStart, expression.Span.Length)))
            {
                InspectOperationValue(operation, callable, identity, inputs);
            }
        }

        public override void VisitLocalFunction(ILocalFunctionOperation operation)
        {
            if (operation.Syntax == callable.Syntax) base.VisitLocalFunction(operation);
        }
    }
}
