using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using System.Collections.Concurrent;
using System.Security.Cryptography;
using System.Text;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal sealed record ScriptTestConsumedInput(string Path, string Identity);

internal static partial class ScriptTestInputDeriver
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
}
