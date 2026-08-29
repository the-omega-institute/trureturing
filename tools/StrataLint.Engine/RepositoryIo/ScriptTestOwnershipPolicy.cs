using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record ScriptTestOwnershipFinding(
    string Path,
    string Message,
    AdmissionEffect Effect);

internal static class ScriptTestOwnershipPolicy
{
    internal const string ProjectName = "StrataLint.ScriptTests";
    internal const string ProjectPath =
        "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
    private const string TestRoot = "tools/tests/StrataLint.ScriptTests/";

    internal static IReadOnlySet<string> DeriveProtectedSubjects(RepositorySnapshot forkPoint) =>
        forkPoint.Files.Keys
            .Select(static path => path.Value)
            .Where(static path => path.EndsWith(".sh", StringComparison.Ordinal)
                || path is "Makefile" or "tools/Makefile")
            .ToImmutableSortedSet(StringComparer.Ordinal);

    internal static string MirrorPath(string subject)
    {
        if (subject.StartsWith("tools/scripts/", StringComparison.Ordinal)
            && subject.EndsWith(".sh", StringComparison.Ordinal))
        {
            return TestRoot + "Scripts/" + subject["tools/scripts/".Length..^3] + ".Tests.cs";
        }

        return subject switch
        {
            "Makefile" => TestRoot + "Makefiles/RootMakefile.Tests.cs",
            "tools/Makefile" => TestRoot + "Makefiles/ToolsMakefile.Tests.cs",
            ".github/scripts/harness-gate.sh" =>
                TestRoot + "Scripts/github/harness-gate.Tests.cs",
            "tools/lean-inspector/inspect.sh" =>
                TestRoot + "Scripts/lean-inspector/inspect.Tests.cs",
            _ => throw new ArgumentException("subject has no script-test mirror rule", nameof(subject)),
        };
    }

    internal static ImmutableArray<ScriptTestOwnershipFinding> Evaluate(
        RepositorySnapshot current,
        RepositorySnapshot forkPoint,
        ScribeTestMap currentMap,
        ScribeTestMap forkPointMap)
    {
        var protectedSubjects = DeriveProtectedSubjects(forkPoint);
        var currentMethods = DeriveMethods(current, currentMap, protectedSubjects);
        var forkPointMethods = DeriveMethods(forkPoint, forkPointMap, protectedSubjects)
            .ToDictionary(static method => method.Identity, StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<ScriptTestOwnershipFinding>();

        foreach (var method in currentMethods.Where(method =>
                     !forkPointMethods.TryGetValue(method.Identity, out var inherited)
                     || inherited.Fingerprint != method.Fingerprint))
        {
            if (method.ProjectPath != ProjectPath)
            {
                if (method.TouchedSubjects.Count != 0 || method.IsUnknown)
                {
                    findings.Add(Finding(
                        method,
                        $"script-touching test method {method.DisplayIdentity} must compile into {ProjectName}"));
                }

                continue;
            }

            if (method.DeclaredSubjects.Count != 1)
            {
                findings.Add(Finding(
                    method,
                    $"script-test unit {method.UnitType} must declare exactly one ScriptSubject; "
                    + $"found {method.DeclaredSubjects.Count}"));
                continue;
            }

            var declared = method.DeclaredSubjects[0];
            if (!protectedSubjects.Contains(declared))
            {
                findings.Add(Finding(
                    method,
                    $"script-test unit {method.UnitType} declares subject {declared}, which is not "
                    + "tracked in the protected base"));
                continue;
            }

            if (method.IsUnknown)
            {
                findings.Add(Finding(
                    method,
                    $"script-test method {method.DisplayIdentity} has an unknown script path; "
                    + "static ownership resolution is fail-closed"));
                continue;
            }

            if (method.TouchedSubjects.Count == 0)
            {
                findings.Add(Finding(
                    method,
                    $"script-test method {method.DisplayIdentity} must statically touch its declared subject {declared}"));
                continue;
            }

            if (method.TouchedSubjects.Count != 1 || method.TouchedSubjects[0] != declared)
            {
                findings.Add(Finding(
                    method,
                    $"script-test unit {method.UnitType} declares {declared}, but method "
                    + $"{method.DisplayIdentity} touches {string.Join(", ", method.TouchedSubjects)}"));
                continue;
            }

            var mirror = MirrorPath(declared);
            if (method.SourcePath != mirror)
            {
                findings.Add(Finding(
                    method,
                    $"runnable fragment for subject {declared} must be in {mirror}"));
            }
        }

        return findings.ToImmutable();
    }

    private static ScriptTestOwnershipFinding Finding(OwnedTestMethod method, string message) =>
        new(method.SourcePath, message, AdmissionEffect.Block);

    private static IReadOnlyList<OwnedTestMethod> DeriveMethods(
        RepositorySnapshot snapshot,
        ScribeTestMap map,
        IReadOnlySet<string> protectedSubjects)
    {
        var sources = map.CompileProjectBySourcePath
            .Where(static item => item.Key.EndsWith(".cs", StringComparison.Ordinal)
                && item.Value.StartsWith("tools/tests/", StringComparison.Ordinal))
            .Select(item => snapshot.TryGetFile(item.Key, out var file)
                ? new ParsedSource(
                    item.Key,
                    item.Value,
                    CSharpSyntaxTree.ParseText(file.Text).GetRoot())
                : null)
            .OfType<ParsedSource>()
            .ToArray();
        var fragments = sources.SelectMany(ParseFragments).ToArray();
        var methodsByCallTarget = fragments.SelectMany(static fragment => fragment.Methods)
            .SelectMany(static method => new[] { method.UnitType, method.SimpleType }
                .Distinct(StringComparer.Ordinal)
                .Select(typeName => new
                {
                    Key = new CallTarget(method.ProjectPath, typeName, method.Name),
                    Method = method,
                }))
            .GroupBy(static item => item.Key)
            .ToDictionary(
                static group => group.Key,
                static group => group.Select(static item => item.Method).ToArray());
        var units = fragments.GroupBy(
                static fragment => new UnitIdentity(fragment.ProjectPath, fragment.UnitType))
            .ToDictionary(
                static group => group.Key,
                static group => new ParsedUnit(group.Key, group.ToArray()));
        var results = new List<OwnedTestMethod>();

        foreach (var unit in units.Values)
        {
            var declaredSubjects = unit.Fragments
                .SelectMany(static fragment => SubjectDeclarations(fragment.Syntax))
                .Order(StringComparer.Ordinal)
                .ToArray();
            var declarationFingerprint = string.Join(
                "\n",
                unit.Fragments.SelectMany(static fragment => fragment.Syntax.AttributeLists)
                    .Select(static attributes => attributes.NormalizeWhitespace().ToFullString())
                    .Order(StringComparer.Ordinal));

            foreach (var runnable in unit.Fragments.SelectMany(static fragment => fragment.Methods)
                         .Where(static method => method.IsRunnable))
            {
                var closure = ReachableMethods(runnable, methodsByCallTarget);
                var mapMethods = map.Methods.Where(method =>
                        method.SourcePath == runnable.SourcePath
                        && method.Id == $"{runnable.SimpleType}.{runnable.Name}")
                    .ToArray();
                var touched = mapMethods.SelectMany(static method => method.Paths)
                    .Concat(closure.SelectMany(method => LiteralProtectedSubjects(
                        method.Syntax,
                        protectedSubjects)))
                    .Where(protectedSubjects.Contains)
                    .Distinct(StringComparer.Ordinal)
                    .Order(StringComparer.Ordinal)
                    .ToArray();
                var isUnknown = mapMethods.Length != 1
                    || mapMethods.Any(static method => method.IsUnknown)
                    || closure.Any(HasUnresolvedRepositoryEnumeration)
                    || closure.Any(method => HasUnresolvedRepositoryPath(method, protectedSubjects))
                    || closure.Any(method => HasUnresolvedExecutionPath(method, protectedSubjects));
                var fingerprint = string.Join(
                    "\n---\n",
                    closure.OrderBy(static method => method.SourcePath, StringComparer.Ordinal)
                        .ThenBy(static method => method.Start)
                        .Select(static method => method.Syntax.NormalizeWhitespace().ToFullString()))
                    + "\n===DECLARATIONS===\n" + declarationFingerprint
                    + "\n===EVIDENCE===\n" + string.Join('\n', touched)
                    + $"\nunknown={isUnknown}";
                results.Add(new OwnedTestMethod(
                    unit.Identity.ProjectPath,
                    runnable.SourcePath,
                    unit.Identity.UnitType,
                    runnable.SimpleType,
                    runnable.Name,
                    runnable.MethodId,
                    fingerprint,
                    declaredSubjects,
                    touched,
                    isUnknown));
            }
        }

        return results;
    }

    private static IEnumerable<ParsedFragment> ParseFragments(ParsedSource source) =>
        source.Root.DescendantNodes().OfType<TypeDeclarationSyntax>().Select(type =>
        {
            var unitType = QualifiedTypeName(type);
            var methods = type.Members.OfType<MethodDeclarationSyntax>().Select(method =>
                new ParsedMethod(
                    source.Path,
                    source.ProjectPath,
                    unitType,
                    type.Identifier.ValueText,
                    method.Identifier.ValueText,
                    MethodId(unitType, method),
                    IsRunnable(method),
                    method.SpanStart,
                    method)).ToArray();
            return new ParsedFragment(source.Path, source.ProjectPath, unitType, type, methods);
        });

    private static string QualifiedTypeName(TypeDeclarationSyntax type)
    {
        var namespaces = type.Ancestors().OfType<BaseNamespaceDeclarationSyntax>()
            .Reverse()
            .Select(static item => item.Name.ToString());
        var types = type.AncestorsAndSelf().OfType<TypeDeclarationSyntax>()
            .Reverse()
            .Select(static item => item.Identifier.ValueText);
        return string.Join('.', namespaces.Concat(types));
    }

    private static string MethodId(string unitType, MethodDeclarationSyntax method) =>
        unitType + "." + method.Identifier.ValueText + "("
        + string.Join(',', method.ParameterList.Parameters.Select(static parameter =>
            parameter.Type?.NormalizeWhitespace().ToFullString() ?? "?")) + ")";

    private static bool IsRunnable(MethodDeclarationSyntax method) =>
        method.AttributeLists.SelectMany(static list => list.Attributes).Any(attribute =>
            AttributeName(attribute) is "Fact" or "FactAttribute" or "Theory" or "TheoryAttribute"
            && attribute.ArgumentList?.Arguments.Any(static argument =>
                argument.NameEquals?.Name.Identifier.ValueText == "Skip"
                && !argument.Expression.IsKind(SyntaxKind.NullLiteralExpression)) != true);

    private static IEnumerable<string> SubjectDeclarations(TypeDeclarationSyntax type)
    {
        foreach (var attribute in type.AttributeLists.SelectMany(static list => list.Attributes)
                     .Where(static attribute => AttributeName(attribute) is
                         "ScriptSubject" or "ScriptSubjectAttribute"))
        {
            var argument = attribute.ArgumentList?.Arguments.SingleOrDefault()?.Expression;
            yield return argument is LiteralExpressionSyntax literal
                && literal.IsKind(SyntaxKind.StringLiteralExpression)
                    ? NormalizePath(literal.Token.ValueText)
                    : "<unresolved>";
        }
    }

    private static string AttributeName(AttributeSyntax attribute) =>
        attribute.Name switch
        {
            IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
            QualifiedNameSyntax qualified => qualified.Right.Identifier.ValueText,
            AliasQualifiedNameSyntax alias => alias.Name.Identifier.ValueText,
            _ => attribute.Name.ToString(),
        };

    private static IReadOnlyList<ParsedMethod> ReachableMethods(
        ParsedMethod root,
        IReadOnlyDictionary<CallTarget, ParsedMethod[]> methodsByCallTarget)
    {
        var pending = new Stack<ParsedMethod>();
        var visited = new HashSet<ParsedMethod>();
        pending.Push(root);
        while (pending.TryPop(out var method))
        {
            if (!visited.Add(method)) continue;
            foreach (var call in Calls(method.Syntax))
            {
                var targetType = call.TargetType ?? method.UnitType;
                if (methodsByCallTarget.TryGetValue(
                        new CallTarget(method.ProjectPath, targetType, call.Name),
                        out var targets))
                {
                    foreach (var target in targets) pending.Push(target);
                }
            }
        }

        return visited.ToArray();
    }

    private static IEnumerable<ParsedCall> Calls(MethodDeclarationSyntax method) =>
        method.DescendantNodes().OfType<InvocationExpressionSyntax>()
            .Select(static invocation => invocation.Expression switch
            {
                IdentifierNameSyntax identifier => new ParsedCall(
                    null,
                    identifier.Identifier.ValueText),
                MemberAccessExpressionSyntax
                {
                    Expression: ThisExpressionSyntax,
                    Name: var name,
                } => new ParsedCall(null, name.Identifier.ValueText),
                MemberAccessExpressionSyntax
                {
                    Expression: ObjectCreationExpressionSyntax creation,
                    Name: var name,
                } => new ParsedCall(creation.Type.ToString(), name.Identifier.ValueText),
                MemberAccessExpressionSyntax member => new ParsedCall(
                    member.Expression.ToString(),
                    member.Name.Identifier.ValueText),
                _ => null,
            })
            .OfType<ParsedCall>();

    private static IEnumerable<string> LiteralProtectedSubjects(
        MethodDeclarationSyntax method,
        IReadOnlySet<string> protectedSubjects)
    {
        var initializers = method.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Where(static variable => variable.Initializer is not null)
            .ToDictionary(
                static variable => variable.Identifier.ValueText,
                static variable => variable.Initializer!.Value,
                StringComparer.Ordinal);
        foreach (var invocation in method.DescendantNodes().OfType<InvocationExpressionSyntax>()
                     .Where(static invocation =>
                         IsExecutionInvocation(invocation)
                         || IsRepositoryAccessInvocation(invocation)))
        {
            foreach (var subject in invocation.ArgumentList.Arguments
                         .SelectMany(argument => ResolveExecutionSubjects(
                             argument.Expression,
                             initializers,
                             protectedSubjects,
                             new HashSet<string>(StringComparer.Ordinal))))
            {
                yield return subject;
            }
        }
    }

    private static IEnumerable<string> ResolveExecutionSubjects(
        ExpressionSyntax expression,
        IReadOnlyDictionary<string, ExpressionSyntax> initializers,
        IReadOnlySet<string> protectedSubjects,
        HashSet<string> visited)
    {
        if (expression is IdentifierNameSyntax identifier
            && visited.Add(identifier.Identifier.ValueText)
            && initializers.TryGetValue(identifier.Identifier.ValueText, out var initializer))
        {
            return ResolveExecutionSubjects(initializer, initializers, protectedSubjects, visited);
        }

        var subjects = new HashSet<string>(StringComparer.Ordinal);
        foreach (var nestedIdentifier in expression.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>())
        {
            var name = nestedIdentifier.Identifier.ValueText;
            if (!visited.Add(name) || !initializers.TryGetValue(name, out var nestedInitializer)) continue;
            subjects.UnionWith(ResolveExecutionSubjects(
                nestedInitializer,
                initializers,
                protectedSubjects,
                visited));
        }

        foreach (var literal in expression.DescendantNodesAndSelf().OfType<LiteralExpressionSyntax>()
                     .Where(static literal => literal.IsKind(SyntaxKind.StringLiteralExpression)))
        {
            var value = NormalizePath(literal.Token.ValueText);
            subjects.UnionWith(protectedSubjects.Where(subject =>
                value.Contains(subject, StringComparison.Ordinal)));
        }

        foreach (var combine in expression.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
                     .Where(static invocation => invocation.Expression is MemberAccessExpressionSyntax
                     {
                         Expression: IdentifierNameSyntax { Identifier.ValueText: "Path" },
                         Name.Identifier.ValueText: "Combine",
                     }))
        {
            var arguments = combine.ArgumentList.Arguments;
            for (var start = 0; start < arguments.Count; start++)
            {
                var suffix = arguments.Skip(start).ToArray();
                if (!suffix.All(static argument => argument.Expression is LiteralExpressionSyntax
                    { RawKind: (int)SyntaxKind.StringLiteralExpression })) continue;
                var value = NormalizePath(string.Join(
                    '/',
                    suffix.Select(static argument =>
                        ((LiteralExpressionSyntax)argument.Expression).Token.ValueText)));
                if (protectedSubjects.Contains(value)) subjects.Add(value);
            }
        }

        return subjects;
    }

    private static bool IsExecutionInvocation(InvocationExpressionSyntax invocation)
    {
        if (invocation.Expression is not MemberAccessExpressionSyntax member) return false;
        var receiver = member.Expression.ToString();
        return member.Name.Identifier.ValueText == "Run"
                && receiver.EndsWith("ProcessRunner", StringComparison.Ordinal)
            || member.Name.Identifier.ValueText == "Start"
                && receiver.EndsWith("Process", StringComparison.Ordinal);
    }

    private static bool IsRepositoryAccessInvocation(InvocationExpressionSyntax invocation)
    {
        if (invocation.Expression is not MemberAccessExpressionSyntax member) return false;
        var receiver = member.Expression.ToString();
        return RepositoryAccessMethods.Contains(member.Name.Identifier.ValueText)
            && (receiver.EndsWith("RepositoryAccessor", StringComparison.Ordinal)
                || receiver is "File" or "System.IO.File");
    }

    private static readonly IReadOnlySet<string> RepositoryAccessMethods =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "Copy",
            "CopyTo",
            "FileExists",
            "OpenRead",
            "ReadAllBytes",
            "ReadAllLines",
            "ReadAllText",
        };

    private static bool HasUnresolvedRepositoryEnumeration(ParsedMethod method) =>
        method.Syntax.DescendantNodes().OfType<InvocationExpressionSyntax>().Any(invocation =>
            invocation.Expression is MemberAccessExpressionSyntax
            {
                Name.Identifier.ValueText: "EnumerateFiles",
                Expression: var receiver,
            }
            && !receiver.ToString().StartsWith("TemporaryFileSystem", StringComparison.Ordinal));

    private static bool HasUnresolvedRepositoryPath(
        ParsedMethod method,
        IReadOnlySet<string> protectedSubjects)
    {
        var initializers = method.Syntax.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Where(static variable => variable.Initializer is not null)
            .ToDictionary(
                static variable => variable.Identifier.ValueText,
                static variable => variable.Initializer!.Value,
                StringComparer.Ordinal);
        return method.Syntax.DescendantNodes().OfType<InvocationExpressionSyntax>()
            .Where(IsRepositoryAccessInvocation)
            .Any(invocation => !invocation.ArgumentList.Arguments.SelectMany(argument =>
                    ResolveExecutionSubjects(
                        argument.Expression,
                        initializers,
                        protectedSubjects,
                        new HashSet<string>(StringComparer.Ordinal)))
                .Any());
    }

    private static bool HasUnresolvedExecutionPath(
        ParsedMethod method,
        IReadOnlySet<string> protectedSubjects)
    {
        var initializers = method.Syntax.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Where(static variable => variable.Initializer is not null)
            .ToDictionary(
                static variable => variable.Identifier.ValueText,
                static variable => variable.Initializer!.Value,
                StringComparer.Ordinal);
        foreach (var invocation in method.Syntax.DescendantNodes().OfType<InvocationExpressionSyntax>()
                     .Where(IsExecutionInvocation))
        {
            if (invocation.ArgumentList.Arguments.SelectMany(argument => ResolveExecutionSubjects(
                    argument.Expression,
                    initializers,
                    protectedSubjects,
                    new HashSet<string>(StringComparer.Ordinal))).Any())
            {
                continue;
            }

            var executableExpression = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression;
            if (!TryResolveString(
                    executableExpression,
                    initializers,
                    new HashSet<string>(StringComparer.Ordinal),
                    out var executable))
            {
                return true;
            }

            var executableName = Path.GetFileName(executable);
            if (string.Equals(executableName, "make", StringComparison.Ordinal)) return true;
            if (!PathConsumingExecutables.Contains(executableName)) continue;
            if (invocation.ArgumentList.Arguments.Skip(1).Take(1).Any(argument =>
                    HasUnresolvedExpression(
                        argument.Expression,
                        initializers,
                        new HashSet<string>(StringComparer.Ordinal))))
            {
                return true;
            }
        }

        return false;
    }

    private static readonly IReadOnlySet<string> PathConsumingExecutables =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "awk",
            "bash",
            "cat",
            "cp",
            "env",
            "head",
            "sed",
            "sh",
            "tail",
            "zsh",
        };

    private static bool HasUnresolvedExpression(
        ExpressionSyntax expression,
        IReadOnlyDictionary<string, ExpressionSyntax> initializers,
        HashSet<string> visited) => expression switch
    {
        LiteralExpressionSyntax => false,
        IdentifierNameSyntax identifier when visited.Add(identifier.Identifier.ValueText)
            && initializers.TryGetValue(identifier.Identifier.ValueText, out var initializer) =>
            HasUnresolvedExpression(initializer, initializers, visited),
        IdentifierNameSyntax => true,
        ParenthesizedExpressionSyntax parenthesized =>
            HasUnresolvedExpression(parenthesized.Expression, initializers, visited),
        BinaryExpressionSyntax binary =>
            HasUnresolvedExpression(binary.Left, initializers, visited)
            || HasUnresolvedExpression(binary.Right, initializers, visited),
        CollectionExpressionSyntax collection => collection.Elements
            .OfType<ExpressionElementSyntax>()
            .Any(element => HasUnresolvedExpression(element.Expression, initializers, visited)),
        ArrayCreationExpressionSyntax array => array.Initializer?.Expressions
            .Any(item => HasUnresolvedExpression(item, initializers, visited)) != false,
        ImplicitArrayCreationExpressionSyntax array => array.Initializer.Expressions
            .Any(item => HasUnresolvedExpression(item, initializers, visited)),
        InterpolatedStringExpressionSyntax interpolated => interpolated.Contents
            .OfType<InterpolationSyntax>()
            .Any(item => HasUnresolvedExpression(item.Expression, initializers, visited)),
        _ => true,
    };

    private static bool TryResolveString(
        ExpressionSyntax? expression,
        IReadOnlyDictionary<string, ExpressionSyntax> initializers,
        HashSet<string> visited,
        out string value)
    {
        if (expression is LiteralExpressionSyntax literal
            && literal.IsKind(SyntaxKind.StringLiteralExpression))
        {
            value = literal.Token.ValueText;
            return true;
        }

        if (expression is IdentifierNameSyntax identifier
            && visited.Add(identifier.Identifier.ValueText)
            && initializers.TryGetValue(identifier.Identifier.ValueText, out var initializer))
        {
            return TryResolveString(initializer, initializers, visited, out value);
        }

        value = string.Empty;
        return false;
    }

    private static string NormalizePath(string path) => path.Replace('\\', '/');

    private sealed record ParsedSource(string Path, string ProjectPath, SyntaxNode Root);
    private sealed record UnitIdentity(string ProjectPath, string UnitType);
    private sealed record ParsedUnit(UnitIdentity Identity, IReadOnlyList<ParsedFragment> Fragments);
    private sealed record ParsedFragment(
        string SourcePath,
        string ProjectPath,
        string UnitType,
        TypeDeclarationSyntax Syntax,
        IReadOnlyList<ParsedMethod> Methods);
    private sealed record ParsedMethod(
        string SourcePath,
        string ProjectPath,
        string UnitType,
        string SimpleType,
        string Name,
        string MethodId,
        bool IsRunnable,
        int Start,
        MethodDeclarationSyntax Syntax);
    private sealed record ParsedCall(string? TargetType, string Name);
    private sealed record CallTarget(string ProjectPath, string UnitType, string Name);
    private sealed record OwnedTestMethod(
        string ProjectPath,
        string SourcePath,
        string UnitType,
        string SimpleType,
        string Name,
        string MethodId,
        string Fingerprint,
        IReadOnlyList<string> DeclaredSubjects,
        IReadOnlyList<string> TouchedSubjects,
        bool IsUnknown)
    {
        internal string Identity => $"{ProjectPath}::{SourcePath}::{MethodId}";
        internal string DisplayIdentity => $"{UnitType}.{Name}";
    }
}
