using System.Buffers.Binary;
using System.Collections;
using System.Collections.Concurrent;
using System.Security.Cryptography;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.Engine;

internal static class ScribeTestMapDeriver
{
    private static readonly ConcurrentDictionary<string, Lazy<ScribeTestMap>> SnapshotDerivations =
        new(StringComparer.Ordinal);
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ScribeTestMap DeriveRepository(string repositoryRoot)
    {
        var tracked = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(file => IsTrackedInput(file.RelativePath))
            .Select(file => new ScribeTrackedSource(file.RelativePath, File.ReadAllText(file.FullPath))).ToArray();
        return DeriveTracked(tracked, EngineeringProjectRegistry.Read(tracked));
    }

    internal static bool IsDerivationInput(string path) =>
        IsTrackedInput(path) || ScribeTestMapEnvironmentProbe.IsBuildInput(path);

    private static bool IsTrackedInput(string path) => path == EngineeringProjectRegistry.ManifestPath
        || path.EndsWith(".cs", StringComparison.Ordinal)
        || path.EndsWith(".csproj", StringComparison.Ordinal)
        || path.EndsWith("packages.lock.json", StringComparison.Ordinal);

    internal static ScribeTestMap DeriveSnapshot(RepositorySnapshot snapshot) =>
        DeriveSnapshot(snapshot, null);

    internal static ScribeTestMap DeriveSnapshot(
        RepositorySnapshot snapshot,
        Func<IEnumerable<ScribeCompilationProject>, IReadOnlyList<string>>? describeInputPaths,
        Func<RepositorySnapshot, ScribeTestMap>? derive = null)
    {
        var metadataDigest = ScribeTestMapStore.ComputeMetadataDigest(snapshot, describeInputPaths);
        var key = SnapshotDerivationKey(snapshot, metadataDigest);
        var candidate = new Lazy<ScribeTestMap>(
            () => derive is null ? DeriveSnapshotUncached(snapshot, describeInputPaths) : derive(snapshot),
            LazyThreadSafetyMode.ExecutionAndPublication);
        var derivation = SnapshotDerivations.GetOrAdd(key, candidate);
        try
        {
            var map = derivation.Value;
            if (!ScribeTestMapStore.MetadataDigestMatches(snapshot, metadataDigest, describeInputPaths))
            {
                RemoveSnapshotDerivation(key, derivation);
            }
            return map;
        }
        catch
        {
            RemoveSnapshotDerivation(key, derivation);
            throw;
        }
    }

    internal static ScribeTestMap DeriveSnapshotUncached(
        RepositorySnapshot snapshot,
        Func<IEnumerable<ScribeCompilationProject>, IReadOnlyList<string>>? describeInputPaths = null)
    {
        var tracked = snapshot.Files.Values.Where(file => IsTrackedInput(file.Path.Value))
            .Select(file => new ScribeTrackedSource(file.Path.Value, file.Text)).ToArray();
        return DeriveTracked(tracked, EngineeringProjectRegistry.Read(tracked), describeInputPaths: describeInputPaths);
    }

    internal static string SnapshotDerivationKey(
        RepositorySnapshot snapshot,
        Func<IEnumerable<ScribeCompilationProject>, IReadOnlyList<string>>? describeInputPaths = null) =>
        SnapshotDerivationKey(snapshot, ScribeTestMapStore.ComputeMetadataDigest(snapshot, describeInputPaths));

    private static string SnapshotDerivationKey(RepositorySnapshot snapshot, string metadataDigest)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        AppendHashString(hash, "snapshot-files");
        AppendHashInt32(hash, snapshot.Files.Count);
        foreach (var file in snapshot.Files.Values.OrderBy(
                     static file => file.Path.Value,
                     StringComparer.Ordinal))
        {
            AppendHashString(hash, file.Path.Value);
            AppendHashBytes(hash, file.RawBytes.AsSpan());
        }

        // Remaining environment/metadata cache inputs are a next-layer boundary.
        var environment = Environment.GetEnvironmentVariables()
            .Cast<DictionaryEntry>()
            .OrderBy(static entry => (string)entry.Key, StringComparer.Ordinal)
            .ToArray();
        AppendHashString(hash, "process-environment");
        AppendHashInt32(hash, environment.Length);
        foreach (var entry in environment)
        {
            AppendHashString(hash, (string)entry.Key);
            AppendHashString(hash, (string?)entry.Value ?? string.Empty);
        }
        AppendHashString(hash, "resolved-temp-path");
        AppendHashString(hash, Path.GetTempPath());
        AppendHashString(hash, "resolved-user-profile");
        AppendHashString(hash, Environment.GetFolderPath(Environment.SpecialFolder.UserProfile));
        AppendHashString(hash, "metadata-digest");
        AppendHashString(hash, metadataDigest);

        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    private static void AppendHashString(IncrementalHash hash, string value) =>
        AppendHashBytes(hash, StrictUtf8.GetBytes(value));

    private static void AppendHashBytes(IncrementalHash hash, ReadOnlySpan<byte> value)
    {
        AppendHashInt32(hash, value.Length);
        hash.AppendData(value);
    }

    private static void AppendHashInt32(IncrementalHash hash, int value)
    {
        Span<byte> bytes = stackalloc byte[sizeof(int)];
        BinaryPrimitives.WriteInt32BigEndian(bytes, value);
        hash.AppendData(bytes);
    }

    private static void RemoveSnapshotDerivation(
        string key,
        Lazy<ScribeTestMap> derivation) =>
        ((ICollection<KeyValuePair<string, Lazy<ScribeTestMap>>>)SnapshotDerivations)
            .Remove(new KeyValuePair<string, Lazy<ScribeTestMap>>(key, derivation));

    // #3670:hang-guard 预算的声明写着「never bears a test verdict」,但那只是**声明** ——
    // 只有走 `TestProcessRunner` 时超时才变成 `SkipException`;走 `BoundedProcessRunner`
    // 时它抛 `TimeoutException`,于是**恰好承担了判词**。本判据把声明与路由钉在一起。
    //
    // **判据的已知反例集合(不完整,逐条写出来)**:本方法按 XML 结构判 `PackageReference` /
    // `AdditionalFiles` / `NoWarn`,故比子串强;但它**看不见**:
    // ① 观察者本身被删除或从 `Compile` 排除(#3416 的 test-identity gap);
    // ② `IncludeAssets`/`ExcludeAssets` 排除 analyzers;
    // ③ `Directory.Build.props` 等继承来的 `NoWarn` / `WarningsNotAsErrors` / ruleset / globalconfig;
    // ④ 经 MSBuild 属性或 import 间接给出的 `Include` 值;
    // ⑤ 源文件内的 `#pragma warning disable RS0030` 与 `.editorconfig` 严重性降级。
    internal static IReadOnlyList<string> FindUnroutedHangGuardCalls(string repositoryRoot)
    {
        var offenders = new List<string>();
        var tracked = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(file => IsTrackedInput(file.RelativePath))
            .Select(file => new ScribeTrackedSource(file.RelativePath, File.ReadAllText(file.FullPath))).ToArray();
        var registry = EngineeringProjectRegistry.Read(tracked);
        var sources = registry.Sources(tracked);
        foreach (var source in registry.Projects.Where(project => project.IsTest)
            .SelectMany(project => sources[project.Path]).DistinctBy(source => source.Path))
        {
            if (!source.Path.EndsWith("/TestProcessRunner.cs", StringComparison.Ordinal))
                offenders.AddRange(UnroutedHangGuardCalls(source.Path, source.Content));
        }

        return offenders.Order(StringComparer.Ordinal).ToArray();
    }

    private static IEnumerable<string> UnroutedHangGuardCalls(string path, string source)
    {
        const string Call = "BoundedProcessRunner.Run(";
        for (var index = source.IndexOf(Call, StringComparison.Ordinal);
             index >= 0;
             index = source.IndexOf(Call, index + Call.Length, StringComparison.Ordinal))
        {
            // raw-string literal 里的示例代码不是真调用。
            if (CountText(source[..index], "\"\"\"") % 2 == 1)
            {
                continue;
            }

            // 取**该调用自己的实参列表**(括号平衡)。固定窗口会跨进相邻调用:
            // 第一版正因此把一处**故意**用 `ZeroDuration` 的调用误报为违规。
            var arguments = BalancedArguments(source, index + Call.Length);
            if (arguments.Contains("HangGuard", StringComparison.Ordinal)
                || arguments.Contains("HangDetectionBudget", StringComparison.Ordinal))
            {
                yield return $"{path}:{CountText(source[..index], "\n") + 1}";
            }
        }
    }

    private static string BalancedArguments(string source, int start)
    {
        var depth = 0;
        for (var index = start; index < source.Length; index++)
        {
            if (source[index] == '(')
            {
                depth++;
            }
            else if (source[index] == ')')
            {
                if (depth == 0)
                {
                    return source[start..index];
                }

                depth--;
            }
        }

        return source[start..];
    }

    private static int CountText(string text, string needle)
    {
        var count = 0;
        var index = text.IndexOf(needle, StringComparison.Ordinal);
        while (index >= 0)
        {
            count++;
            index = text.IndexOf(needle, index + needle.Length, StringComparison.Ordinal);
        }

        return count;
    }

    internal static ScribeTestMap DeriveTracked(
        IReadOnlyList<ScribeTrackedSource> tracked,
        EngineeringProjectRegistry registry,
        ScribeBindingStrategy bindingStrategy = ScribeBindingStrategy.Demand,
        IScribeBindingRecorder? recorder = null,
        Func<IEnumerable<ScribeCompilationProject>, IReadOnlyList<string>>? describeInputPaths = null)
    {
        var context = ScribeProjectCompilationContext.Create(tracked, registry)
            with { DescribeMetadataInputs = describeInputPaths };
        var testPaths = registry.Projects.Where(project => project.IsTest).Select(project => project.Path).ToHashSet(StringComparer.Ordinal);
        var testSources = context.Projects.Where(project => testPaths.Contains(project.Path))
            .SelectMany(project => project.Sources.Select(source => new TestMapSource(source.Path,
                source.Content, project.TestPartitionKey!))).ToArray();
        return DeriveSources(testSources, [], productionAssemblies: context.ProductionAssemblies,
            compilationContext: context, bindingStrategy: bindingStrategy, recorder: recorder);
    }

    internal static ScribeTestMap DeriveSources(
        IEnumerable<TestMapSource> sourceFiles,
        IEnumerable<(string Path, int Line)> indirectProductionSites,
        IReadOnlySet<string>? productionAssemblies = null,
        ScribeProjectCompilationContext? compilationContext = null,
        ScribeBindingStrategy bindingStrategy = ScribeBindingStrategy.Demand,
        IScribeBindingRecorder? recorder = null)
    {
        var parsed = ScribeTestSymbolBinder.Bind(
            sourceFiles,
            bindingStrategy,
            productionAssemblies,
            compilationContext,
            recorder).ToArray();
        var discoveryCriteria = ExtractDiscoveryCriteria(parsed);
        var methods = parsed.SelectMany(static source => source.Callables).ToArray();
        var indirect = indirectProductionSites.ToArray();
        var results = new List<ScribeTestMethod>();

        foreach (var test in methods.Where(static method => method.IsTest))
        {
            var reasons = new HashSet<TestMapUnknownReason>();
            var pending = new Stack<ScribeBoundCallable>();
            var visited = new HashSet<ScribeBoundCallable>();
            pending.Push(test);
            while (pending.TryPop(out var method))
            {
                if (!visited.Add(method))
                {
                    continue;
                }

                if (!method.IsProductionSource)
                {
                    InspectMethod(method, discoveryCriteria, reasons);
                }
                reasons.UnionWith(method.BindingUnknownReasons);
                if (indirect.Any(site => site.Path == method.Path
                    && method.ContainsLine(site.Line)))
                {
                    reasons.Add(TestMapUnknownReason.IndirectViaProductionLoader);
                }

                foreach (var target in method.Targets)
                {
                    pending.Push(target);
                }
            }

            results.Add(new ScribeTestMethod(
                test.PartitionKey,
                test.Path,
                $"{test.TypeName}.{test.Name}",
                reasons.Order().ToArray()));
        }

        return new ScribeTestMap(
            results
                .OrderBy(static method => method.PartitionKey, StringComparer.Ordinal)
                .ThenBy(static method => method.SourcePath, StringComparer.Ordinal)
                .ThenBy(static method => method.Id, StringComparer.Ordinal)
                .ToArray());
    }

    private static void InspectMethod(
        ScribeBoundCallable method,
        IReadOnlySet<string> discoveryCriteria,
        HashSet<TestMapUnknownReason> reasons)
    {
        var model = method.SemanticModel;
        foreach (var invocation in method.InspectionNodes.OfType<InvocationExpressionSyntax>())
        {
            if (IsAccessorCall(invocation, model, "Discover"))
            {
                InspectDiscovery(invocation, discoveryCriteria, reasons);
            }

            if (IsAccessorCall(invocation, model, "EnumerateDeclared"))
            {
                if (!HasLiteralDeclaredPrefix(invocation))
                {
                    reasons.Add(TestMapUnknownReason.VariablePath);
                }
                continue;
            }

            if (IsAccessorCall(invocation, model, "EnumerateFiles"))
            {
                var enumerationArgument = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression;
                if (enumerationArgument is not null
                    && ScribePathProvenance.IsNonRepository(
                        enumerationArgument,
                        model,
                        method.SemanticModels))
                {
                    continue;
                }
                reasons.Add(TestMapUnknownReason.DirectoryEnumeration);
                InspectRepositoryPath(enumerationArgument, model, method.SemanticModels, reasons);
                continue;
            }

            if (!IsAccessorCall(
                    invocation,
                    model,
                    "ReadAllText",
                    "ReadAllBytes",
                    "FileExists",
                    "CopyTo"))
            {
                continue;
            }

            if (IsAccessorCall(invocation, model, "ReadAllText", "ReadAllBytes")
                && IsDeclaredEnumerationFullPath(
                    invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression,
                    model))
            {
                continue;
            }

            var argument = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression;
            if (argument is not null
                && ScribePathProvenance.IsNonRepository(argument, model, method.SemanticModels))
            {
                continue;
            }

            InspectRepositoryPath(argument, model, method.SemanticModels, reasons);
        }
    }

    private static bool HasLiteralDeclaredPrefix(InvocationExpressionSyntax invocation)
    {
        var arguments = invocation.ArgumentList.Arguments;
        return arguments.Count >= 2
            && arguments[1].Expression is LiteralExpressionSyntax literal
            && literal.IsKind(SyntaxKind.StringLiteralExpression);
    }

    private static bool IsDeclaredEnumerationFullPath(
        ExpressionSyntax? argument,
        SemanticModel model)
    {
        if (argument is not MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax entry,
                Name.Identifier.ValueText: "FullPath",
            })
        {
            return false;
        }

        var selector = argument.Ancestors().OfType<SimpleLambdaExpressionSyntax>()
            .FirstOrDefault(lambda =>
                lambda.Parameter.Identifier.ValueText == entry.Identifier.ValueText);
        if (selector?.Parent is not ArgumentSyntax
            {
                Parent: ArgumentListSyntax
                {
                    Parent: InvocationExpressionSyntax select,
                },
            })
        {
            return false;
        }

        if (select.Expression is not MemberAccessExpressionSyntax
            {
                Name.Identifier.ValueText: "Select",
                Expression: var source,
            })
        {
            return false;
        }

        while (source is InvocationExpressionSyntax invocation)
        {
            if (IsAccessorCall(invocation, model, "EnumerateDeclared"))
            {
                return HasLiteralDeclaredPrefix(invocation);
            }

            if (invocation.Expression is not MemberAccessExpressionSyntax member)
            {
                return false;
            }

            source = member.Expression;
        }

        return false;
    }

    private static void InspectRepositoryPath(
        ExpressionSyntax? argument,
        SemanticModel model,
        ScribeSemanticModelProvider semanticModels,
        HashSet<TestMapUnknownReason> reasons)
    {
        var create = argument
            ?
            .DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
            .FirstOrDefault(static candidate => candidate.Expression is MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax { Identifier.ValueText: "RepositoryRelativePath" },
                Name.Identifier.ValueText: "Create",
            });
        var expression = create?.ArgumentList.Arguments.SingleOrDefault()?.Expression;
        if (IsConstantString(expression, model))
        {
            return;
        }

        if (IsLiteralCombinedRepositoryPath(argument, model, semanticModels))
        {
            return;
        }

        reasons.Add(TestMapUnknownReason.VariablePath);
    }

    private static bool IsLiteralCombinedRepositoryPath(
        ExpressionSyntax? expression,
        SemanticModel model,
        ScribeSemanticModelProvider semanticModels)
    {
        if (expression is InvocationExpressionSyntax combine
            && model.GetSymbolInfo(combine).Symbol is IMethodSymbol
            {
                Name: "Combine",
                ContainingType: { } pathType,
            }
            && pathType.ToDisplayString() == "System.IO.Path"
            && combine.ArgumentList.Arguments is { Count: >= 2 } arguments
            && ScribeTestSymbolBinder.IsRepositoryRootExpression(
                arguments[0].Expression, model, semanticModels))
        {
            foreach (var argument in arguments.Skip(1))
            {
                if (!IsConstantString(argument.Expression, model))
                {
                    return false;
                }
            }

            return true;
        }

        return false;
    }

    private static bool IsConstantString(ExpressionSyntax? expression, SemanticModel model) =>
        expression is not null
        && model.GetConstantValue(expression) is { HasValue: true, Value: string };

    private static void InspectDiscovery(
        InvocationExpressionSyntax invocation,
        IReadOnlySet<string> discoveryCriteria,
        HashSet<TestMapUnknownReason> reasons)
    {
        var criterion = (invocation.ArgumentList.Arguments.LastOrDefault()?.Expression
            as MemberAccessExpressionSyntax)?.Name.Identifier.ValueText;
        if (criterion is not null
            && discoveryCriteria.Contains(criterion))
        {
            return;
        }

        reasons.Add(TestMapUnknownReason.RepositoryRootMarker);
    }

    private static IReadOnlySet<string> ExtractDiscoveryCriteria(
        IEnumerable<ScribeParsedSource> sources)
    {
        var result = new HashSet<string>(StringComparer.Ordinal);
        var matches = sources.SelectMany(static source => source.Root.DescendantNodes()
            .OfType<MethodDeclarationSyntax>())
            .Where(static method => method.Identifier.ValueText == "Matches");
        foreach (var arm in matches.SelectMany(static method => method.DescendantNodes()
                     .OfType<SwitchExpressionArmSyntax>()))
        {
            var criteria = arm.Pattern.DescendantNodesAndSelf()
                .OfType<MemberAccessExpressionSyntax>()
                .Where(static member => member.Expression is IdentifierNameSyntax
                {
                    Identifier.ValueText: "RepositoryRootCriterion",
                })
                .Select(static member => member.Name.Identifier.ValueText)
                .Distinct(StringComparer.Ordinal)
                .ToArray();
            if (criteria.Length == 0)
            {
                continue;
            }

            if (MarkerPathsAreLiteral(arm.Expression))
            {
                result.UnionWith(criteria);
            }
        }

        return result;
    }

    private static bool MarkerPathsAreLiteral(ExpressionSyntax expression)
    {
        var combines = expression.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
            .Where(static invocation => invocation.Expression is MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax { Identifier.ValueText: "Path" },
                Name.Identifier.ValueText: "Combine",
            })
            .ToArray();
        foreach (var combine in combines)
        {
            var arguments = combine.ArgumentList.Arguments;
            if (arguments.Count < 2
                || arguments[0].Expression is not IdentifierNameSyntax { Identifier.ValueText: "root" })
            {
                return false;
            }

            foreach (var argument in arguments.Skip(1))
            {
                if (argument.Expression is not LiteralExpressionSyntax literal
                    || !literal.IsKind(SyntaxKind.StringLiteralExpression))
                {
                    return false;
                }
            }
        }

        return combines.Length != 0;
    }

    private static bool IsAccessorCall(
        InvocationExpressionSyntax invocation,
        SemanticModel model,
        params string[] names)
    {
        if (model.GetSymbolInfo(invocation).Symbol is not IMethodSymbol method
            || !names.Contains(method.Name, StringComparer.Ordinal))
        {
            return false;
        }

        if (!method.Locations.Any(static location => location.IsInSource))
        {
            var owner = method.ContainingType.ToDisplayString();
            return owner == "System.IO.File"
                || owner == "System.IO.Directory" && method.Name == "EnumerateFiles";
        }

        if (method.Name == "EnumerateDeclared"
            && method.Parameters.Length >= 2
            && method.Parameters[0].Type.SpecialType == SpecialType.System_String
            && method.Parameters[1].Type.SpecialType == SpecialType.System_String)
        {
            return true;
        }

        return IsRepositoryAccessorContract(method.ContainingType);
    }

    private static bool IsRepositoryAccessorContract(INamedTypeSymbol type) =>
        type.GetMembers().OfType<IPropertySymbol>().Any(static property =>
            property.Type.GetMembers().OfType<IPropertySymbol>().Any(static nested =>
                nested.Type.SpecialType == SpecialType.System_String
                && nested.Name == "FullPath"))
        && type.GetMembers().OfType<IMethodSymbol>().Any(method =>
            method.IsStatic
            && method.Name == "Discover"
            && SymbolEqualityComparer.Default.Equals(method.ReturnType, type));

}
