using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal sealed record WallClockAssertionFinding(string Path, int Line, string Message);

internal static class WallClockAssertionPolicy
{
    private static readonly string[] TestProjectPrefixes =
    [
        "Meta/StrataLint/StrataLint.Tests/",
        "Meta/StrataLint/StrataLint.Scribe.Tests/",
        "Meta/StrataLint/StrataLint.ArchitectureTests/",
    ];

    // This syntax policy follows direct expressions and local-variable assignments within one
    // callable. Recognized flows that escape that boundary fail closed with this marker.
    internal const string CoverageGap =
        "ASSUMED-UNVERIFIED: wall-clock flow escapes local assertion analysis";

    internal static IReadOnlyList<WallClockAssertionFinding> InspectRepository(string repositoryRoot) =>
        CSharpRepositorySources.Enumerate(repositoryRoot)
            .Where(static source => TestProjectPrefixes.Any(prefix =>
                source.RelativePath.StartsWith(prefix, StringComparison.Ordinal)))
            .SelectMany(source => InspectSource(source.RelativePath, File.ReadAllText(source.FullPath)))
            .ToArray();

    internal static IReadOnlyList<WallClockAssertionFinding> InspectSource(string path, string source)
    {
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        var findings = new List<WallClockAssertionFinding>();

        foreach (var callable in root.DescendantNodes().Where(static node =>
                     node is BaseMethodDeclarationSyntax or LocalFunctionStatementSyntax
                         or AnonymousFunctionExpressionSyntax))
        {
            var taintedLocals = FindTaintedLocals(callable);
            findings.AddRange(FindEscapingFlows(path, callable, taintedLocals));
            foreach (var assertion in callable.DescendantNodes().OfType<InvocationExpressionSyntax>()
                         .Where(IsAssertionRoot))
            {
                var judgedExpression = IsXunitAssertion(assertion)
                    ? (SyntaxNode)assertion.ArgumentList
                    : assertion.FirstAncestorOrSelf<ExpressionStatementSyntax>()?.Expression ?? assertion;
                if (!ContainsWallClock(judgedExpression, taintedLocals))
                {
                    continue;
                }

                var line = assertion.GetLocation().GetLineSpan().StartLinePosition.Line + 1;
                findings.Add(new WallClockAssertionFinding(
                    path,
                    line,
                    $"{path}:{line}: assertion depends on a wall-clock value"));
            }
        }

        return findings
            .DistinctBy(static finding => (finding.Path, finding.Line))
            .ToArray();
    }

    private static IEnumerable<WallClockAssertionFinding> FindEscapingFlows(
        string path,
        SyntaxNode callable,
        IReadOnlySet<string> taintedLocals)
    {
        var localNames = callable.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Select(static variable => variable.Identifier.ValueText)
            .ToHashSet(StringComparer.Ordinal);
        var parameterNames = callable.DescendantNodes().OfType<ParameterSyntax>()
            .Select(static parameter => parameter.Identifier.ValueText)
            .ToHashSet(StringComparer.Ordinal);
        var returns = callable.DescendantNodes().OfType<ReturnStatementSyntax>()
            .Where(statement => statement.Expression is not null
                && ContainsWallClock(statement.Expression, taintedLocals))
            .Cast<SyntaxNode>();
        var nonlocalAssignments = callable.DescendantNodes().OfType<AssignmentExpressionSyntax>()
            .Where(assignment => (assignment.Left is not IdentifierNameSyntax identifier
                    || !localNames.Contains(identifier.Identifier.ValueText)
                    && !parameterNames.Contains(identifier.Identifier.ValueText))
                && ContainsWallClock(assignment.Right, taintedLocals))
            .Cast<SyntaxNode>();
        var refParameterAssignments = callable.DescendantNodes().OfType<AssignmentExpressionSyntax>()
            .Where(assignment => assignment.Left is IdentifierNameSyntax identifier
                && callable.DescendantNodes().OfType<ParameterSyntax>().Any(parameter =>
                    parameter.Identifier.ValueText == identifier.Identifier.ValueText
                    && parameter.Modifiers.Any(modifier => modifier.Kind() is SyntaxKind.RefKeyword or SyntaxKind.OutKeyword))
                && ContainsWallClock(assignment.Right, taintedLocals))
            .Cast<SyntaxNode>();
        var refOrOutArguments = callable.DescendantNodes().OfType<ArgumentSyntax>()
            .Where(argument => argument.RefKindKeyword.Kind() is SyntaxKind.RefKeyword or SyntaxKind.OutKeyword
                && ContainsWallClock(argument.Expression, taintedLocals))
            .Cast<SyntaxNode>();

        foreach (var node in returns.Concat(nonlocalAssignments).Concat(refParameterAssignments).Concat(refOrOutArguments))
        {
            var line = node.GetLocation().GetLineSpan().StartLinePosition.Line + 1;
            yield return new WallClockAssertionFinding(path, line, $"{path}:{line}: {CoverageGap}");
        }
    }

    private static HashSet<string> FindTaintedLocals(SyntaxNode callable)
    {
        var tainted = new HashSet<string>(StringComparer.Ordinal);
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var variable in callable.DescendantNodes().OfType<VariableDeclaratorSyntax>())
            {
                if (variable.Initializer is not null
                    && ContainsWallClock(variable.Initializer.Value, tainted))
                {
                    changed |= tainted.Add(variable.Identifier.ValueText);
                }
            }

            foreach (var assignment in callable.DescendantNodes().OfType<AssignmentExpressionSyntax>())
            {
                if (assignment.Left is IdentifierNameSyntax identifier
                    && ContainsWallClock(assignment.Right, tainted))
                {
                    changed |= tainted.Add(identifier.Identifier.ValueText);
                }
            }
        }

        return tainted;
    }

    private static bool IsAssertionRoot(InvocationExpressionSyntax invocation) =>
        IsXunitAssertion(invocation) || IsShouldInvocation(invocation);

    private static bool IsXunitAssertion(InvocationExpressionSyntax invocation) =>
        invocation.Expression is MemberAccessExpressionSyntax
        {
            Expression: IdentifierNameSyntax { Identifier.ValueText: "Assert" },
        };

    private static bool IsShouldInvocation(InvocationExpressionSyntax invocation) =>
        invocation.Expression is MemberAccessExpressionSyntax
        {
            Name.Identifier.ValueText: "Should",
        };

    private static bool ContainsWallClock(SyntaxNode node, IReadOnlySet<string> taintedLocals) =>
        node.DescendantNodesAndSelf().Any(candidate =>
            candidate is IdentifierNameSyntax identifier
                && taintedLocals.Contains(identifier.Identifier.ValueText)
            || IsWallClockSource(candidate));

    private static bool IsWallClockSource(SyntaxNode node)
    {
        if (node is InvocationExpressionSyntax
            {
                Expression: MemberAccessExpressionSyntax
                {
                    Expression: IdentifierNameSyntax { Identifier.ValueText: "Stopwatch" },
                    Name.Identifier.ValueText: "StartNew" or "GetTimestamp",
                },
            })
        {
            return true;
        }

        return node is MemberAccessExpressionSyntax member
            && (member.Name.Identifier.ValueText is "Elapsed" or "ElapsedTicks"
                || member is
                {
                    Expression: IdentifierNameSyntax { Identifier.ValueText: "DateTime" },
                    Name.Identifier.ValueText: "Now" or "UtcNow",
                }
                || member is
                {
                    Expression: IdentifierNameSyntax { Identifier.ValueText: "Environment" },
                    Name.Identifier.ValueText: "TickCount" or "TickCount64",
                });
    }
}
