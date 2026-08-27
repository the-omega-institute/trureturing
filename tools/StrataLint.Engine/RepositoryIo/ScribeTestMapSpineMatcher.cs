using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.Engine;

// The only modeled fluent read shape for tracked test sources. Keeping this
// structural matcher together makes the accepted spine and its fail-closed
// boundary explicit without mixing it with map derivation responsibilities.
internal static class ScribeTestMapSpineMatcher
{
    internal static bool TryAddBoundedTrackedTestEnumeration(
        InvocationExpressionSyntax invocation,
        HashSet<string> paths,
        HashSet<TestMapUnknownReason> reasons)
    {
        if (invocation.Expression is not MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax { Identifier.ValueText: "GitIndexRepositoryFiles" },
                Name.Identifier.ValueText: "Enumerate",
            }
            || invocation.ArgumentList.Arguments is not { Count: 1 } arguments
            || !IsRepositoryLayoutFindRoot(arguments[0].Expression))
        {
            return false;
        }

        if (!TryGetFollowingOperator(invocation, "Where", out var where)
            || !TryGetSingleParameterExpressionLambda(where, out var filterParameter, out var filter)
            || !IsBoundedTrackedFilter(filter, filterParameter)
            || !TryGetFollowingOperator(where, "Select", out var select)
            || !TryGetSingleParameterExpressionLambda(select, out var selectorParameter, out var selector)
            || !IsBoundedTrackedSelector(selector, selectorParameter)
            || !TryGetFollowingOperator(select, "ToArray", out var terminal)
            || terminal.ArgumentList.Arguments.Count != 0
            || HasFollowingOperator(terminal))
        {
            reasons.Add(TestMapUnknownReason.Other);
            return true;
        }

        paths.Add("tools/tests");
        return true;
    }

    private static bool TryGetFollowingOperator(
        ExpressionSyntax source,
        string operatorName,
        out InvocationExpressionSyntax invocation)
    {
        invocation = null!;
        if (source.Parent is not MemberAccessExpressionSyntax member
            || !ReferenceEquals(member.Expression, source)
            || member.Name.Identifier.ValueText != operatorName
            || member.Parent is not InvocationExpressionSyntax candidate
            || !ReferenceEquals(candidate.Expression, member))
        {
            return false;
        }

        invocation = candidate;
        return true;
    }

    private static bool HasFollowingOperator(ExpressionSyntax source) =>
        source.Parent is MemberAccessExpressionSyntax member
        && ReferenceEquals(member.Expression, source)
        && member.Parent is InvocationExpressionSyntax invocation
        && ReferenceEquals(invocation.Expression, member);

    private static bool TryGetSingleParameterExpressionLambda(
        InvocationExpressionSyntax invocation,
        out string parameter,
        out ExpressionSyntax body)
    {
        parameter = string.Empty;
        body = null!;
        if (invocation.ArgumentList.Arguments is not { Count: 1 } arguments)
        {
            return false;
        }

        switch (arguments[0].Expression)
        {
            case SimpleLambdaExpressionSyntax { Body: ExpressionSyntax expression } lambda:
                parameter = lambda.Parameter.Identifier.ValueText;
                body = expression;
                return parameter.Length != 0;
            case ParenthesizedLambdaExpressionSyntax
                {
                    ParameterList.Parameters: { Count: 1 } parameters,
                    Body: ExpressionSyntax expression,
                }:
                parameter = parameters[0].Identifier.ValueText;
                body = expression;
                return parameter.Length != 0;
            default:
                return false;
        }
    }

    private static bool IsBoundedTrackedFilter(ExpressionSyntax body, string parameter) =>
        TryInspectBoundedTrackedFilter(body, parameter, out var hasBoundary)
        && hasBoundary;

    private static bool TryInspectBoundedTrackedFilter(
        ExpressionSyntax expression,
        string parameter,
        out bool hasBoundary)
    {
        hasBoundary = false;
        if (expression is ParenthesizedExpressionSyntax parenthesized)
        {
            return TryInspectBoundedTrackedFilter(parenthesized.Expression, parameter, out hasBoundary);
        }

        if (expression is BinaryExpressionSyntax conjunction
            && conjunction.IsKind(SyntaxKind.LogicalAndExpression))
        {
            var leftIsValid = TryInspectBoundedTrackedFilter(
                conjunction.Left,
                parameter,
                out var leftHasBoundary);
            var rightIsValid = TryInspectBoundedTrackedFilter(
                conjunction.Right,
                parameter,
                out var rightHasBoundary);
            hasBoundary = leftHasBoundary || rightHasBoundary;
            return leftIsValid && rightIsValid;
        }

        if (expression is InvocationExpressionSyntax call
            && IsRelativePathStringPredicate(call, parameter))
        {
            hasBoundary = IsRelativePathStringPredicate(
                call,
                parameter,
                requiredMethod: "StartsWith",
                requiredLiteral: "tools/tests/");
            return true;
        }

        if (expression is PrefixUnaryExpressionSyntax negation
            && negation.IsKind(SyntaxKind.LogicalNotExpression)
            && negation.Operand is InvocationExpressionSyntax negatedCall)
        {
            return IsRelativePathStringPredicate(negatedCall, parameter);
        }

        if (expression is BinaryExpressionSyntax comparison
            && comparison.IsKind(SyntaxKind.NotEqualsExpression))
        {
            return (IsParameterMember(comparison.Left, parameter, "RelativePath")
                    && IsFixedFilterValue(comparison.Right))
                || (IsParameterMember(comparison.Right, parameter, "RelativePath")
                    && IsFixedFilterValue(comparison.Left));
        }

        return false;
    }

    private static bool IsFixedFilterValue(ExpressionSyntax expression) =>
        expression is IdentifierNameSyntax
        || expression is LiteralExpressionSyntax literal
            && literal.IsKind(SyntaxKind.StringLiteralExpression);

    private static bool IsRelativePathStringPredicate(
        InvocationExpressionSyntax invocation,
        string parameter,
        string? requiredMethod = null,
        string? requiredLiteral = null)
    {
        if (invocation.Expression is not MemberAccessExpressionSyntax
            {
                Expression: MemberAccessExpressionSyntax
                {
                    Expression: IdentifierNameSyntax receiver,
                    Name.Identifier.ValueText: "RelativePath",
                },
                Name: var method,
            }
            || receiver.Identifier.ValueText != parameter
            || method.Identifier.ValueText is not ("StartsWith" or "EndsWith")
            || (requiredMethod is not null && method.Identifier.ValueText != requiredMethod)
            || invocation.ArgumentList.Arguments is not { Count: 2 } arguments
            || arguments[0].Expression is not LiteralExpressionSyntax literal
            || !literal.IsKind(SyntaxKind.StringLiteralExpression)
            || (requiredLiteral is not null && literal.Token.ValueText != requiredLiteral)
            || !IsNamedMember(arguments[1].Expression, "StringComparison", "Ordinal"))
        {
            return false;
        }

        return true;
    }

    private static bool IsBoundedTrackedSelector(ExpressionSyntax body, string parameter)
    {
        if (ContainsUnsupportedBranching(body))
        {
            return false;
        }

        var calls = body.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>().ToArray();
        var reads = calls
            .Where(call => IsBoundedTrackedContentRead(call, parameter))
            .ToArray();
        if (reads.Length != 1)
        {
            return false;
        }

        var read = reads[0];
        var fullPathReferences = body.DescendantNodesAndSelf()
            .OfType<MemberAccessExpressionSyntax>()
            .Where(static member => member.Name.Identifier.ValueText == "FullPath")
            .ToArray();
        return fullPathReferences.Length == 1
            && ReferenceEquals(
                fullPathReferences[0],
                read.ArgumentList.Arguments[0].Expression)
            && calls.All(call => ReferenceEquals(call, read)
                || IsModeledReadLinesProjection(call, read, parameter));
    }

    private static bool ContainsUnsupportedBranching(ExpressionSyntax body) =>
        body.DescendantNodesAndSelf().Any(static node =>
            node is AnonymousFunctionExpressionSyntax
                or ConditionalExpressionSyntax
                or SwitchExpressionSyntax
                or QueryExpressionSyntax
                or AssignmentExpressionSyntax
                or AwaitExpressionSyntax);

    private static bool IsModeledReadLinesProjection(
        InvocationExpressionSyntax invocation,
        InvocationExpressionSyntax read,
        string parameter) =>
        IsBoundedFileReadLines(read, parameter)
        && invocation.Expression is MemberAccessExpressionSyntax
        {
            Expression: var owner,
            Name.Identifier.ValueText: "Join",
        }
        && IsStringTypeName(owner)
        && invocation.ArgumentList.Arguments is { Count: 2 } arguments
        && arguments[0].Expression is LiteralExpressionSyntax separator
        && (separator.IsKind(SyntaxKind.CharacterLiteralExpression)
            || separator.IsKind(SyntaxKind.StringLiteralExpression))
        && ReferenceEquals(arguments[1].Expression, read);

    private static bool IsStringTypeName(ExpressionSyntax expression) =>
        expression is PredefinedTypeSyntax { Keyword.ValueText: "string" }
        or IdentifierNameSyntax { Identifier.ValueText: "String" };

    private static bool IsNamedMember(
        ExpressionSyntax expression,
        string owner,
        string member) => expression is MemberAccessExpressionSyntax
        {
            Expression: IdentifierNameSyntax type,
            Name: IdentifierNameSyntax name,
        }
        && type.Identifier.ValueText == owner
        && name.Identifier.ValueText == member;

    private static bool IsParameterMember(
        ExpressionSyntax expression,
        string parameter,
        string member) => expression is MemberAccessExpressionSyntax
        {
            Expression: IdentifierNameSyntax receiver,
            Name: IdentifierNameSyntax name,
        }
        && receiver.Identifier.ValueText == parameter
        && name.Identifier.ValueText == member;

    private static bool IsRepositoryLayoutFindRoot(ExpressionSyntax expression) =>
        expression is InvocationExpressionSyntax
        {
            Expression: MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax { Identifier.ValueText: "RepositoryLayout" },
                Name.Identifier.ValueText: "FindRoot",
            },
            ArgumentList.Arguments.Count: 0,
        };

    private static bool IsBoundedTrackedContentRead(
        InvocationExpressionSyntax invocation,
        string boundedParameter) =>
        IsBoundedXDocumentLoad(invocation, boundedParameter)
        || IsBoundedFileReadLines(invocation, boundedParameter);

    private static bool IsBoundedXDocumentLoad(
        InvocationExpressionSyntax invocation,
        string boundedParameter)
    {
        if (invocation.Expression is not MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax { Identifier.ValueText: "XDocument" },
                Name.Identifier.ValueText: "Load",
            }
            || invocation.ArgumentList.Arguments is not { Count: 1 or 2 } arguments
            || !IsParameterMember(arguments[0].Expression, boundedParameter, "FullPath")
            || (arguments.Count == 2
                && !IsNamedMember(arguments[1].Expression, "LoadOptions", "None")))
        {
            return false;
        }

        return true;
    }

    private static bool IsBoundedFileReadLines(
        InvocationExpressionSyntax invocation,
        string boundedParameter) => invocation.Expression is MemberAccessExpressionSyntax
        {
            Expression: IdentifierNameSyntax { Identifier.ValueText: "File" },
            Name.Identifier.ValueText: "ReadLines",
        }
        && invocation.ArgumentList.Arguments is { Count: 1 } arguments
        && IsParameterMember(arguments[0].Expression, boundedParameter, "FullPath");
}
