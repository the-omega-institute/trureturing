using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using System.Collections.Concurrent;
using System.Security.Cryptography;
using System.Text;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal sealed record ScriptTestConsumedInput(string Path, string Identity);

internal static class ScriptTestInputDeriver
{
    private static readonly ConcurrentDictionary<string, Lazy<IReadOnlyList<ScriptTestConsumedInput>>>
        Cache = new(StringComparer.Ordinal);

    internal static IReadOnlyList<ScriptTestConsumedInput> Derive(
        RepositorySnapshot snapshot,
        ScriptTestProjectClosure projectClosure)
    {
        var key = SnapshotKey(snapshot);
        var candidate = new Lazy<IReadOnlyList<ScriptTestConsumedInput>>(
            () => DeriveUncached(snapshot, projectClosure),
            LazyThreadSafetyMode.ExecutionAndPublication);
        var derivation = Cache.GetOrAdd(key, candidate);
        try
        {
            return derivation.Value;
        }
        catch
        {
            ((ICollection<KeyValuePair<string, Lazy<IReadOnlyList<ScriptTestConsumedInput>>>>)Cache)
                .Remove(new KeyValuePair<string, Lazy<IReadOnlyList<ScriptTestConsumedInput>>>(key, derivation));
            throw;
        }
    }

    private static IReadOnlyList<ScriptTestConsumedInput> DeriveUncached(
        RepositorySnapshot snapshot,
        ScriptTestProjectClosure projectClosure)
    {
        var compileMap = QueryCompileItems(snapshot, projectClosure.Projects);
        if (compileMap.Findings.Count != 0)
        {
            throw new InvalidDataException(
                "ScriptTests gate compile query failed: "
                + string.Join(" | ", compileMap.Findings.Select(static finding =>
                    $"{finding.Path}: {finding.Message}")));
        }

        var reached = projectClosure.Projects.ToHashSet(StringComparer.Ordinal);
        var compilationLocks = projectClosure.Projects
            .Where(project => snapshot.TryGetFile(project, out var file)
                && XDocument.Parse(file.Text, LoadOptions.None).Descendants().Any(
                    static element => element.Name.LocalName == "PackageReference"))
            .Select(static project => project[..project.LastIndexOf('/')] + "/packages.lock.json")
            .ToHashSet(StringComparer.Ordinal);
        var tracked = snapshot.Files.Values
            .Where(file => reached.Contains(file.Path.Value)
                || compilationLocks.Contains(file.Path.Value)
                || file.Path.Value.EndsWith(".cs", StringComparison.Ordinal)
                    && compileMap.ProjectBySourcePath.TryGetValue(file.Path.Value, out var owner)
                    && reached.Contains(owner))
            .Select(static file => new ScribeTrackedSource(file.Path.Value, file.Text))
            .ToArray();
        var testSources = tracked
            .Where(source => source.Path.EndsWith(".cs", StringComparison.Ordinal)
                && compileMap.ProjectBySourcePath.GetValueOrDefault(source.Path)
                    == ScriptTestGateClosurePolicy.ProjectPath)
            .Select(static source => new TestMapSource(
                source.Path,
                source.Content,
                ScriptTestGateClosurePolicy.ProjectPath))
            .ToArray();
        if (testSources.Length == 0)
            throw new InvalidDataException("ScriptTests gate has no compiled test sources");

        var testProjects = projectClosure.Projects
            .Where(project => snapshot.TryGetFile(project, out var file)
                && ScribeProjectCompilationContext.IsXunitProject(file.Text))
            .ToHashSet(StringComparer.Ordinal);
        var context = ScribeProjectCompilationContext.Create(
            tracked,
            compileMap.ProjectBySourcePath,
            testProjects);
        var parsed = ScribeTestSymbolBinder.Bind(
            testSources,
            context.ProductionAssemblies,
            context);
        return Inspect(parsed);
    }

    private static string SnapshotKey(RepositorySnapshot snapshot)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        foreach (var file in snapshot.Files.Values.OrderBy(
                     static file => file.Path.Value,
                     StringComparer.Ordinal))
        {
            hash.AppendData(Encoding.UTF8.GetBytes(file.Path.Value));
            hash.AppendData([0]);
            hash.AppendData(file.RawBytes.AsSpan());
            hash.AppendData([0]);
        }
        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    private static MsBuildCompileMap QueryCompileItems(
        RepositorySnapshot snapshot,
        IReadOnlyList<string> projects)
    {
        try
        {
            using var checkout = MsBuildCompileOracle.Materialize(snapshot);
            var entry = MsBuildCompileOracle.Query(
                checkout.Root,
                [ScriptTestGateClosurePolicy.ProjectPath]);
            var owners = entry.ProjectBySourcePath
                .Where(static pair => pair.Key.StartsWith(
                    "tools/tests/StrataLint.ScriptTests/",
                    StringComparison.Ordinal))
                .ToDictionary(static pair => pair.Key, static pair => pair.Value, StringComparer.Ordinal);
            var directories = projects
                .Select(project => (Project: project, Directory: project[..project.LastIndexOf('/')]))
                .Where(static item => item.Project != ScriptTestGateClosurePolicy.ProjectPath)
                .OrderByDescending(static item => item.Directory.Length)
                .ToArray();
            foreach (var file in snapshot.Files.Values.Where(static file =>
                         file.Path.Value.EndsWith(".cs", StringComparison.Ordinal)))
            {
                var owner = directories.FirstOrDefault(item => file.Path.Value.StartsWith(
                    item.Directory + "/",
                    StringComparison.Ordinal)).Project;
                if (owner is not null
                    && !file.Path.Value.Contains("/bin/", StringComparison.Ordinal)
                    && !file.Path.Value.Contains("/obj/", StringComparison.Ordinal))
                {
                    owners[file.Path.Value] = owner;
                }
            }
            return new MsBuildCompileMap(owners, entry.Findings);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            return new MsBuildCompileMap(
                new Dictionary<string, string>(StringComparer.Ordinal),
                [new MsBuildCompileFinding(
                    ScriptTestGateClosurePolicy.ProjectPath,
                    $"snapshot materialization failed closed: {exception.Message}")]);
        }
    }

    private static IReadOnlyList<ScriptTestConsumedInput> Inspect(
        IReadOnlyList<ScribeParsedSource> parsed)
    {
        var inputs = new Dictionary<string, string>(StringComparer.Ordinal);
        var tests = parsed.SelectMany(static source => source.Callables)
            .Where(static callable => callable.IsTest)
            .ToArray();
        if (tests.Length == 0)
            throw new InvalidDataException("ScriptTests gate has no bound test identities");

        foreach (var test in tests)
        {
            var identity = $"{test.TypeName}.{test.Name}";
            var pending = new Stack<ScribeBoundCallable>();
            var visited = new HashSet<ScribeBoundCallable>();
            pending.Push(test);
            while (pending.TryPop(out var callable))
            {
                if (!visited.Add(callable)) continue;
                if (callable.BindingUnknownReasons.Contains(
                        TestMapUnknownReason.IndirectViaProductionLoader))
                {
                    throw Failure(identity, "production-loader");
                }
                InspectCallable(callable, identity, inputs);
                foreach (var target in callable.Targets) pending.Push(target);
            }

            if (visited.Any(static callable => callable.BindingUnknownReasons.Contains(
                    TestMapUnknownReason.MetadataUnavailable)))
            {
                throw Failure(identity, "metadata-unavailable");
            }
        }

        return inputs
            .Select(static pair => new ScriptTestConsumedInput(pair.Key, pair.Value))
            .OrderBy(static input => input.Path, StringComparer.Ordinal)
            .ThenBy(static input => input.Identity, StringComparer.Ordinal)
            .ToArray();
    }

    private static void InspectCallable(
        ScribeBoundCallable callable,
        string identity,
        IDictionary<string, string> inputs)
    {
        // Audited scope: repository-rooted values in the Roslyn operation trees of statically
        // bound, test-reachable C# callables. Each value is accepted only by a recognised
        // consumer or non-consuming carrier; other uses found by that walk are rejected.
        // Known-open bypasses -- open(案号待开):
        // - Reflection and dynamic dispatch can hide a consuming operation from the bound tree.
        // - Source-generated code absent from the snapshot compilation and non-C# carriers are not walked.
        // - Runtime-only callable edges outside ScribeTestSymbolBinder's bound graph are not walked.
        // - Compiler value carriers in the non-consuming bucket have no callable symbol; their
        //   allowance is broader than symbol identity and is valid only while the value remains
        //   in the walked tree. Reflection, dynamic dispatch, or another carrier can still hide its exit.
        // - A future build or test-selection change can skip this audit; this source cannot prove its execution.
        var walker = new RepositoryValueWalker(callable, identity, inputs);
        foreach (var node in callable.InspectionNodes)
            walker.Visit(callable.SemanticModel.GetOperation(node));
    }

    private static void InspectOperationValue(
        IOperation operation,
        ScribeBoundCallable callable,
        string identity,
        IDictionary<string, string> inputs)
    {
        if (operation.Type is null
            || operation.Kind == OperationKind.ObjectOrCollectionInitializer
            || operation.Syntax is not ExpressionSyntax expression
            || !IsRepositoryOperand(expression, callable))
        {
            return;
        }

        var use = FindOperationUse(operation);
        if (use.Consumer is IInvocationOperation invocation)
        {
            InspectInvocationValue(invocation, use.ParameterOrdinal, expression, callable, identity, inputs);
            return;
        }
        if (use.Consumer is IObjectCreationOperation creation)
        {
            if (creation.Constructor?.ContainingType.ToDisplayString()
                == "System.Diagnostics.ProcessStartInfo")
            {
                AddResolved(expression, callable, identity, inputs);
                return;
            }
            RejectOperationValue(identity, creation, callable.SemanticModel);
            return;
        }
        if (use.Consumer is ISimpleAssignmentOperation assignment)
        {
            if (assignment.Target is IPropertyReferenceOperation property
                && IsProcessStartInfoProperty(property.Property, "FileName", "Arguments"))
            {
                AddResolved(expression, callable, identity, inputs);
                return;
            }
            RejectOperationValue(identity, assignment, callable.SemanticModel);
            return;
        }
        if (use.Consumer is IPropertyReferenceOperation { Property.IsIndexer: true } indexer)
        {
            RejectOperationValue(identity, indexer, callable.SemanticModel);
            return;
        }
        if (IsNonConsumingCompilerCarrier(use.Consumer)) return;
        RejectOperationValue(identity, use.Consumer ?? operation, callable.SemanticModel);
    }

    private static void InspectInvocationValue(
        IInvocationOperation invocation,
        int? parameterOrdinal,
        ExpressionSyntax expression,
        ScribeBoundCallable callable,
        string identity,
        IDictionary<string, string> inputs)
    {
        var method = invocation.TargetMethod;
        if (IsDirectoryEnumeration(method)) throw Failure(identity, "directory-enumeration");
        if (IsPathTransformation(method)) return;
        if (IsTestProcessRunner(method) && parameterOrdinal == 2)
        {
            InspectRepositoryWorkingDirectoryOperands(
                invocation,
                expression,
                callable,
                identity,
                inputs);
            return;
        }
        if (IsConsumingInvocation(
                (InvocationExpressionSyntax)invocation.Syntax,
                method,
                parameterOrdinal,
                callable.SemanticModel))
        {
            var operands = IsTestProcessRunner(method) && parameterOrdinal == 1
                ? StringCollectionOperands(expression, callable.SemanticModel)
                : [expression];
            foreach (var operand in operands)
                AddResolved(operand, callable, identity, inputs);
            return;
        }
        RejectOperationValue(identity, invocation, callable.SemanticModel);
    }

    private static void InspectRepositoryWorkingDirectoryOperands(
        IInvocationOperation invocation,
        ExpressionSyntax workingDirectoryExpression,
        ScribeBoundCallable callable,
        string identity,
        IDictionary<string, string> inputs)
    {
        var workingDirectory = ResolvePath(
            workingDirectoryExpression,
            callable.SemanticModel,
            callable.SemanticModels,
            new HashSet<ISymbol>(SymbolEqualityComparer.Default));
        if (workingDirectory.Kind is not (PathValueKind.RepositoryRoot or PathValueKind.RepositoryPath))
        {
            throw Failure(
                identity,
                $"unresolved repository working directory ({workingDirectoryExpression.GetType().Name})");
        }

        foreach (var operand in TestProcessRunnerCommandOperands(invocation, callable.SemanticModel))
        {
            if (ScribePathProvenance.IsNonRepository(
                    operand,
                    callable.SemanticModel,
                    callable.SemanticModels))
            {
                continue;
            }

            var value = ResolvePath(
                operand,
                callable.SemanticModel,
                callable.SemanticModels,
                new HashSet<ISymbol>(SymbolEqualityComparer.Default));
            if (value.Kind == PathValueKind.RepositoryPath)
            {
                if (!IsGeneratedControllerOperand(value.Value!))
                    inputs.TryAdd(value.Value!, identity);
                continue;
            }
            if (value.Kind == PathValueKind.Literal
                && IsRelativePathShaped(value.Value!))
            {
                inputs.TryAdd(
                    ResolveAgainstRepositoryWorkingDirectory(
                        workingDirectory,
                        value.Value!,
                        operand,
                        identity),
                    identity);
                continue;
            }
            if (value.Kind == PathValueKind.Unknown
                && HasRelativePathEvidence(operand, callable.SemanticModel))
            {
                throw Failure(
                    identity,
                    $"unresolved repository working-directory command operand "
                    + $"({operand.GetType().Name})");
            }
        }
    }

    private static IEnumerable<ExpressionSyntax> TestProcessRunnerCommandOperands(
        IInvocationOperation invocation,
        SemanticModel model)
    {
        foreach (var argument in invocation.Arguments.Where(static argument =>
                     argument.Parameter?.Ordinal is 0 or 1))
        {
            if (argument.Value.Syntax is not ExpressionSyntax expression) continue;
            if (argument.Parameter?.Ordinal == 0)
            {
                yield return expression;
                continue;
            }
            foreach (var operand in StringCollectionOperands(expression, model))
                yield return operand;
        }
    }

    private static bool HasRelativePathEvidence(ExpressionSyntax expression, SemanticModel model)
    {
        if (model.GetConstantValue(expression) is { HasValue: true, Value: string constant })
            return IsRelativePathShaped(constant);
        if (expression is not InvocationExpressionSyntax invocation
            || BoundMethod(invocation, model) is not { } method
            || method.ContainingType.ToDisplayString() != "System.IO.Path"
            || method.Name != "Combine"
            || invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression is not { } first
            || model.GetConstantValue(first) is not { HasValue: true, Value: string prefix })
        {
            return false;
        }
        return IsRelativeOperand(prefix) && invocation.ArgumentList.Arguments.Count >= 2;
    }

    private static bool IsRelativePathShaped(string value) =>
        IsRelativeOperand(value)
        && (value.Contains('/', StringComparison.Ordinal)
            || value.Contains('\\', StringComparison.Ordinal));

    private static bool IsRelativeOperand(string value) =>
        !string.IsNullOrWhiteSpace(value)
        && !value.StartsWith("-", StringComparison.Ordinal)
        && !value.StartsWith("/", StringComparison.Ordinal)
        && !value.StartsWith("\\", StringComparison.Ordinal)
        && !(value.Length >= 3
            && char.IsLetter(value[0])
            && value[1] == ':'
            && value[2] is '/' or '\\');

    private static string ResolveAgainstRepositoryWorkingDirectory(
        PathValue workingDirectory,
        string relative,
        ExpressionSyntax expression,
        string identity)
    {
        var segments = workingDirectory.Kind == PathValueKind.RepositoryPath
            ? workingDirectory.Value!.Split('/').ToList()
            : [];
        foreach (var segment in relative.Replace('\\', '/').Split('/'))
        {
            if (segment is "" or ".") continue;
            if (segment == "..")
            {
                if (segments.Count == 0)
                {
                    throw Failure(
                        identity,
                        $"repository working-directory command operand escapes repository "
                        + $"({expression.GetType().Name})");
                }
                segments.RemoveAt(segments.Count - 1);
                continue;
            }
            segments.Add(segment);
        }
        if (segments.Count == 0)
        {
            throw Failure(
                identity,
                $"empty repository working-directory command operand ({expression.GetType().Name})");
        }
        return string.Join('/', segments);
    }

    private static OperationUse FindOperationUse(IOperation operation)
    {
        var current = operation;
        while (current.Parent is { } parent
            && (parent is IConversionOperation or IParenthesizedOperation
                || IsTransparentCompilerCarrier(parent)))
        {
            current = parent;
        }
        if (current.Parent is IArgumentOperation argument)
            return new OperationUse(argument.Parent, argument.Parameter?.Ordinal);
        return new OperationUse(current.Parent, null);
    }

    private static bool IsTransparentCompilerCarrier(IOperation? operation) => operation is
        IArrayCreationOperation or IArrayInitializerOperation or ICollectionExpressionOperation
        or IInterpolatedStringOperation or IInterpolationOperation or IConditionalOperation
        or ICoalesceOperation
        || operation is IBinaryOperation
        {
            Type.SpecialType: SpecialType.System_String,
        };

    private static bool IsNonConsumingCompilerCarrier(IOperation? operation) => operation is
        IVariableInitializerOperation or IFieldInitializerOperation or IPropertyInitializerOperation
        || IsTransparentCompilerCarrier(operation);

    private static void RejectOperationValue(
        string identity,
        IOperation operation,
        SemanticModel model)
    {
        var symbol = operation switch
        {
            IInvocationOperation invocation => invocation.TargetMethod.ToDisplayString(),
            IObjectCreationOperation creation => creation.Constructor?.ToDisplayString() ?? "<unbound>",
            IPropertyReferenceOperation property => property.Property.ToDisplayString(),
            ISimpleAssignmentOperation { Target: IPropertyReferenceOperation property } =>
                property.Property.ToDisplayString(),
            _ => model.GetSymbolInfo(operation.Syntax).Symbol?.ToDisplayString() ?? operation.Kind.ToString(),
        };
        throw Failure(identity, $"unrecognised-sink operation value: {symbol}");
    }

    private static bool IsRepositoryOperand(
        ExpressionSyntax expression,
        ScribeBoundCallable callable)
    {
        if (!IsPathBearing(expression, callable.SemanticModel)
            || ScribePathProvenance.IsNonRepository(
                expression,
                callable.SemanticModel,
                callable.SemanticModels))
        {
            return false;
        }

        var value = ResolvePath(
            expression,
            callable.SemanticModel,
            callable.SemanticModels,
            new HashSet<ISymbol>(SymbolEqualityComparer.Default));
        return value.Kind is PathValueKind.RepositoryRoot or PathValueKind.RepositoryPath
            || value.Kind == PathValueKind.Unknown && CanCarryRepositoryRootEvidence(
                expression,
                callable.SemanticModel)
                && ScribeTestSymbolBinder.IsRepositoryRootExpression(
                    expression,
                    callable.SemanticModel);
    }

    private static bool CanCarryRepositoryRootEvidence(
        ExpressionSyntax expression,
        SemanticModel model) => expression switch
    {
        IdentifierNameSyntax or InterpolatedStringExpressionSyntax or BinaryExpressionSyntax
            or MemberAccessExpressionSyntax => true,
        InvocationExpressionSyntax invocation => IsPathTransformation(BoundMethod(invocation, model)),
        _ => false,
    };

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
            if (owner == "StrataLint.Tests.TestRepositoryLayout" && method.Name == "FindRoot")
                return PathValue.RepositoryRoot;
            if (owner == "System.IO.Path" && method.Name == "Combine")
                return ResolveCombine(invocation, model, models, visited);
            if (owner == "System.IO.Path" && method.Name is "GetFullPath" or "GetDirectoryName")
                return invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression is { } argument
                    ? ResolvePath(argument, model, models, visited)
                    : PathValue.Unknown;
            if (owner == "StrataLint.Tests.RepositoryRelativePath" && method.Name == "Create")
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
        return owner == "StrataLint.Tests.ScriptHarnessScratch"
                && method.Name == "CopyScriptInto" && parameterOrdinal == 0
            || owner == "StrataLint.Tests.TestProcessRunner"
                && method.Name == "Run" && parameterOrdinal is 0 or 1
            || IsProcessStartInfoArgumentListAdd(invocation, method, model)
                && parameterOrdinal == 0
            || owner == "StrataLint.Tests.TestRepositoryLayout"
                && method.Name == "ReadAllText" && parameterOrdinal == 0
            || owner == "System.IO.File"
                && method.Name is "ReadAllText" or "ReadAllBytes" or "ReadAllLines"
                && parameterOrdinal == 0
            || owner == "System.IO.File" && method.Name == "Copy" && parameterOrdinal == 0;
    }

    private static bool IsTestProcessRunner(IMethodSymbol? method) =>
        method?.ContainingType.ToDisplayString() == "StrataLint.Tests.TestProcessRunner"
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
