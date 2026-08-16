using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal static partial class RemoteStateIndependencePolicy
{
    private static readonly IReadOnlySet<string> HttpQueryMethods =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "GetAsync",
            "GetByteArrayAsync",
            "GetStreamAsync",
            "GetStringAsync",
            "PostAsync",
            "SendAsync",
        };

    private static IEnumerable<RemoteStateFinding> InspectProcessInvocation(
        string path,
        InvocationExpressionSyntax invocation,
        IReadOnlyDictionary<string, string> constants,
        IReadOnlySet<string> realRoots)
    {
        if (invocation.Expression is MemberAccessExpressionSyntax member
            && RightmostName(member.Expression) == "BoundedProcessRunner"
            && member.Name.Identifier.ValueText == "Run")
        {
            foreach (var finding in InspectBoundedProcessRun(
                         path,
                         invocation,
                         constants,
                         realRoots))
            {
                yield return finding;
            }
        }

        if (HttpQueryMethods.Contains(InvocationName(invocation))
            && UsesHttpClient(invocation, invocation.SyntaxTree.GetRoot())
            && invocation.ArgumentList.Arguments.FirstOrDefault() is { } uriArgument)
        {
            if (!TryConstantString(uriArgument.Expression, constants, out var uri)
                || IsRepositoryApiUrl(uri))
            {
                yield return Finding(
                    path,
                    invocation,
                    "remote API",
                    TryConstantString(uriArgument.Expression, constants, out uri)
                        ? $"test queries live repository API '{uri}'"
                        : "test HTTP query target is not provably independent of live repository state");
            }
        }
    }

    private static IEnumerable<RemoteStateFinding> InspectBoundedProcessRun(
        string path,
        InvocationExpressionSyntax invocation,
        IReadOnlyDictionary<string, string> constants,
        IReadOnlySet<string> realRoots)
    {
        var callArguments = invocation.ArgumentList.Arguments;
        if (callArguments.Count < 2
            || !TryConstantString(callArguments[0].Expression, constants, out var executable))
        {
            yield break;
        }

        var argumentsKnown = TryStringCollection(
            callArguments[1].Expression,
            constants,
            out var arguments);
        if (IsExecutable(executable, "git")
            && callArguments.Count >= 3
            && DependsOnRealRepository(callArguments[2].Expression, realRoots))
        {
            if (!argumentsKnown)
            {
                yield return Finding(
                    path,
                    invocation,
                    "git command",
                    "real repository git arguments are not statically provable as remote-independent");
                yield break;
            }

            foreach (var finding in InspectGitArguments(path, invocation, arguments))
            {
                yield return finding;
            }
        }

        if (IsExecutable(executable, "gh")
            && (!argumentsKnown || arguments.Count != 0
                && RemoteApiCommands.Contains(arguments[0] ?? string.Empty)))
        {
            yield return Finding(
                path,
                invocation,
                "remote API",
                "test invokes GitHub CLI against live repository state");
        }

        if ((IsExecutable(executable, "curl") || IsExecutable(executable, "wget"))
            && (!argumentsKnown || arguments.OfType<string>().Any(IsRepositoryApiUrl)))
        {
            yield return Finding(
                path,
                invocation,
                "remote API",
                "test process queries a live repository API");
        }
    }

    private static IEnumerable<RemoteStateFinding> InspectProcessStartInfos(
        string path,
        SyntaxNode root)
    {
        foreach (var variable in root.DescendantNodes().OfType<VariableDeclaratorSyntax>())
        {
            if (variable.Initializer?.Value is not ObjectCreationExpressionSyntax creation
                || RightmostName(creation.Type) != "ProcessStartInfo"
                || creation.ArgumentList?.Arguments.FirstOrDefault() is not { } executableArgument)
            {
                continue;
            }

            var name = variable.Identifier.ValueText;
            var method = variable.FirstAncestorOrSelf<BaseMethodDeclarationSyntax>();
            if (method is null)
            {
                continue;
            }
            var constants = DeriveStringConstants(method);
            var realRoots = DeriveRealRepositoryVariables(method);
            if (!TryConstantString(executableArgument.Expression, constants, out var executable))
            {
                continue;
            }

            var workingDirectories = creation.Initializer?.Expressions
                    .OfType<AssignmentExpressionSyntax>()
                    .Where(static assignment => assignment.Left is IdentifierNameSyntax { Identifier.ValueText: "WorkingDirectory" })
                    .Select(static assignment => assignment.Right)
                    .Concat(method.DescendantNodes().OfType<AssignmentExpressionSyntax>()
                        .Where(assignment => IsMemberOf(assignment.Left, name, "WorkingDirectory"))
                        .Select(static assignment => assignment.Right))
                ?? [];
            var usesRealRepository = workingDirectories.Any(expression =>
                DependsOnRealRepository(expression, realRoots));
            if (!usesRealRepository)
            {
                continue;
            }

            var arguments = creation.ArgumentList.Arguments.Skip(1)
                .Select(static argument => argument.Expression)
                .Concat(method.DescendantNodes().OfType<InvocationExpressionSyntax>()
                    .Where(invocation => invocation.Expression is MemberAccessExpressionSyntax add
                        && add.Name.Identifier.ValueText == "Add"
                        && IsMemberOf(add.Expression, name, "ArgumentList"))
                    .SelectMany(static invocation => invocation.ArgumentList.Arguments
                        .Select(static argument => argument.Expression)))
                .Select(expression => TryConstantString(expression, constants, out var value)
                    ? value
                    : null)
                .ToArray();

            if (IsExecutable(executable, "git"))
            {
                foreach (var finding in InspectGitArguments(path, creation, arguments))
                {
                    yield return finding;
                }
            }
        }
    }

    private static bool UsesHttpClient(
        InvocationExpressionSyntax invocation,
        SyntaxNode root)
    {
        if (invocation.Expression is not MemberAccessExpressionSyntax member)
        {
            return false;
        }
        if (member.Expression is ObjectCreationExpressionSyntax creation)
        {
            return RightmostName(creation.Type) == "HttpClient";
        }
        if (member.Expression is not IdentifierNameSyntax identifier)
        {
            return false;
        }

        return root.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Any(variable => variable.Identifier.ValueText == identifier.Identifier.ValueText
                && variable.Parent is VariableDeclarationSyntax declaration
                && (RightmostName(declaration.Type) == "HttpClient"
                    || variable.Initializer?.Value is ObjectCreationExpressionSyntax client
                        && RightmostName(client.Type) == "HttpClient"));
    }

    private static bool TryStringCollection(
        ExpressionSyntax expression,
        IReadOnlyDictionary<string, string> constants,
        out IReadOnlyList<string?> values)
    {
        IEnumerable<ExpressionSyntax>? elements = expression switch
        {
            CollectionExpressionSyntax collection => collection.Elements
                .OfType<ExpressionElementSyntax>().Select(static element => element.Expression),
            ArrayCreationExpressionSyntax array => array.Initializer?.Expressions,
            ImplicitArrayCreationExpressionSyntax implicitArray => implicitArray.Initializer.Expressions,
            _ => null,
        };
        if (elements is null)
        {
            values = [];
            return false;
        }

        var resolved = elements.Select(item => TryConstantString(item, constants, out var value)
                ? value
                : null)
            .ToArray();
        values = resolved;
        return resolved.All(static value => value is not null);
    }

    private static bool IsMemberOf(ExpressionSyntax expression, string receiver, string member) =>
        expression is MemberAccessExpressionSyntax access
        && access.Name.Identifier.ValueText == member
        && access.Expression is IdentifierNameSyntax identifier
        && identifier.Identifier.ValueText == receiver;
}
