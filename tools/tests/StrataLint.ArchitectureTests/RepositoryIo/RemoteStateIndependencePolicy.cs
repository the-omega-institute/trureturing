using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using StrataLint.Engine;
using System.Text.RegularExpressions;

namespace StrataLint.ArchitectureTests;

internal sealed record RemoteStateSource(string Path, string Content);

internal sealed record RemoteStateFinding(string Path, int Line, string Operation, string Message)
{
    internal string Location => $"{Path}:{Line}";
    public override string ToString() =>
        $"{Location}: {Operation}: early-feedback shape match, not a remote-unreachability proof: {Message}";
}

/// <summary>
/// Gives local and pull-request-time feedback for recognized remote-dependent shapes in C# tests.
/// It can fail before a push reaches CI, but it is not a proof that no remote-reading execution
/// path exists.
/// </summary>
/// <remarks>
/// Carrier families outside a completeness claim include C# helper-argument indirection,
/// reflection through <c>GetMethod("ReadRevision").Invoke</c>, property-assigned
/// <c>ProcessStartInfo</c>, MSBuild <c>Exec</c> in project files, and event-payload revisions such
/// as <c>github.event.before</c> (only its direct audited shape has a regression match). Unexecuted
/// hypotheses intentionally not modeled here include composite and JavaScript actions, source
/// generators, P/Invoke, PowerShell, Python, Make, <c>eval</c>/<c>bash -c</c>, and revisions read
/// from files or environment variables. The post-checkout strip step removes every checkout remote
/// and every <c>refs/remotes/*</c> ref before verdict code runs, which eliminates name-based
/// resolution but not remote reachability: <c>fetch-depth: 0</c> leaves every branch's objects in
/// the local object database, so a raw OID recorded before the strip still resolves. See CLAUDE.md
/// for the measured boundary; do not restate either layer as a completeness guarantee.
///
/// Scope narrowed on 2026-08-29: the workflow-YAML side of this scan was retired together with
/// every other workflow test (see <c>WorkflowTestProhibitionTests</c>). A workflow shape assertion
/// only proves what the file looks like, never whether the step runs — this repository measured
/// exactly that when <c>if: false</c> on the strip step left all 16 covering tests green. Workflow
/// behaviour is verified by running it on a real event (CLAUDE.md 器律⑦), not from a unit test.
/// </remarks>
internal static partial class RemoteStateIndependencePolicy
{
    private static readonly IReadOnlySet<string> AllowedRevisions =
        new HashSet<string>(StringComparer.Ordinal) { "HEAD", "HEAD^1" };
    private static readonly IReadOnlySet<string> RevisionReaders =
        new HashSet<string>(StringComparer.Ordinal) { "ReadRevision", "ReadRevisionFile" };
    private static readonly IReadOnlySet<string> RemoteGitCommands =
        new HashSet<string>(StringComparer.Ordinal) { "fetch", "ls-remote", "pull" };
    private static readonly IReadOnlySet<string> RevisionGitCommands = new HashSet<string>(StringComparer.Ordinal)
    {
        "branch", "cat-file", "checkout", "diff", "log", "ls-tree", "merge-base",
        "reset", "rev-parse", "show", "switch",
    };
    private static readonly IReadOnlySet<string> RemoteApiCommands = new HashSet<string>(StringComparer.Ordinal)
    {
        "api", "issue", "pr", "release", "repo", "run", "search", "workflow",
    };
    private static readonly IReadOnlySet<string> HttpQueryMethods = new HashSet<string>(StringComparer.Ordinal)
    {
        "GetAsync", "GetByteArrayAsync", "GetStreamAsync", "GetStringAsync", "PostAsync", "SendAsync",
    };

    internal static IReadOnlyList<RemoteStateFinding> InspectRepository(string repositoryRoot)
    {
        var findings = new List<RemoteStateFinding>();
        foreach (var file in GitIndexRepositoryFiles.Enumerate(repositoryRoot))
        {
            if (file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            {
                findings.AddRange(InspectTestSource(new(file.RelativePath, File.ReadAllText(file.FullPath))));
            }
        }
        return findings.OrderBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.Line).ThenBy(static item => item.Operation, StringComparer.Ordinal).ToArray();
    }

    internal static IReadOnlyList<RemoteStateFinding> InspectTestSource(RemoteStateSource source)
    {
        var tree = CSharpSyntaxTree.ParseText(source.Content);
        var root = tree.GetRoot();
        var findings = tree.GetDiagnostics().Where(static item => item.Severity == DiagnosticSeverity.Error)
            .Select(item => new RemoteStateFinding(source.Path,
                item.Location.GetLineSpan().StartLinePosition.Line + 1, "unrecognized C#", item.GetMessage()))
            .ToList();

        foreach (var invocation in root.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            var scope = Scope(invocation, root);
            var method = InvocationName(invocation);
            if (RevisionReaders.Contains(method) && UsesRealGateway(invocation, scope))
            {
                var revision = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression;
                if (revision is null || !IsAllowedRevision(revision))
                {
                    findings.Add(Finding(source.Path, invocation, "disallowed revision",
                        "real checkout revision is not head or base (HEAD or HEAD^1)"));
                }
            }
            if (method == "InspectAdmissionTopology" && UsesRealGateway(invocation, scope))
            {
                findings.Add(Finding(source.Path, invocation, "remote API",
                    "real checkout topology inspection calls git ls-remote"));
            }

            findings.AddRange(InspectProcessInvocation(source.Path, invocation, scope));
            if (HttpQueryMethods.Contains(method) && UsesHttpClient(invocation, scope))
            {
                var target = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression;
                if (target is null || !TryLiteral(target, out var uri) || IsRepositoryApiUrl(uri))
                {
                    findings.Add(Finding(source.Path, invocation, "remote API",
                        "test HTTP query is not proven independent of live repository state"));
                }
            }
        }
        findings.AddRange(InspectProcessStartInfos(source.Path, root));
        return findings;
    }

    private static IEnumerable<RemoteStateFinding> InspectProcessInvocation(
        string path, InvocationExpressionSyntax invocation, SyntaxNode scope)
    {
        var call = invocation.ArgumentList.Arguments;
        if (InvocationName(invocation) == "RunGit" && call.Count >= 2
            && IsRealCheckout(call[0].Expression, scope))
        {
            foreach (var finding in InspectGit(path, invocation,
                         call.Skip(1).Select(static item => LiteralOrNull(item.Expression)).ToArray()))
                yield return finding;
        }
        if (InvocationName(invocation) != "Run"
            || invocation.Expression is not MemberAccessExpressionSyntax run
            || RightmostName(run.Expression) != "BoundedProcessRunner" || call.Count < 2
            || !TryLiteral(call[0].Expression, out var executable))
            yield break;

        if (IsExecutable(executable, "git") && call.Count >= 3 && IsRealCheckout(call[2].Expression, scope))
        {
            if (!TryStrings(call[1].Expression, out var args))
            {
                yield return Finding(path, invocation, "git command",
                    "real checkout git command is not statically known");
                yield break;
            }
            foreach (var finding in InspectGit(path, invocation, args)) yield return finding;
        }
        else if (TryStrings(call[1].Expression, out var args) && IsExecutable(executable, "gh")
                 && (args.Count == 0 || RemoteApiCommands.Contains(args[0] ?? string.Empty)))
        {
            yield return Finding(path, invocation, "remote API",
                "test invokes GitHub CLI against live repository state");
        }
        else if ((IsExecutable(executable, "curl") || IsExecutable(executable, "wget"))
                 && args.OfType<string>().Any(IsRepositoryApiUrl))
        {
            yield return Finding(path, invocation, "remote API", "test process queries a live repository API");
        }
    }

    private static IEnumerable<RemoteStateFinding> InspectProcessStartInfos(string path, SyntaxNode root)
    {
        foreach (var variable in root.DescendantNodes().OfType<VariableDeclaratorSyntax>())
        {
            if (variable.Initializer?.Value is not ObjectCreationExpressionSyntax creation
                || RightmostName(creation.Type) != "ProcessStartInfo"
                || creation.ArgumentList?.Arguments.FirstOrDefault() is not { } executable
                || !TryLiteral(executable.Expression, out var name) || !IsExecutable(name, "git")
                || variable.FirstAncestorOrSelf<BaseMethodDeclarationSyntax>() is not { } method)
                continue;
            var workingDirectories = creation.Initializer?.Expressions.OfType<AssignmentExpressionSyntax>()
                .Where(static item => item.Left is IdentifierNameSyntax { Identifier.ValueText: "WorkingDirectory" })
                .Select(static item => item.Right) ?? [];
            if (!workingDirectories.Any(item => IsRealCheckout(item, method))) continue;

            var receiver = variable.Identifier.ValueText;
            var args = creation.ArgumentList.Arguments.Skip(1).Select(static item => item.Expression)
                .Concat(method.DescendantNodes().OfType<InvocationExpressionSyntax>()
                    .Where(item => item.Expression is MemberAccessExpressionSyntax add
                        && add.Name.Identifier.ValueText == "Add"
                        && IsMember(add.Expression, receiver, "ArgumentList"))
                    .SelectMany(static item => item.ArgumentList.Arguments.Select(static arg => arg.Expression)))
                .Select(LiteralOrNull).ToArray();
            foreach (var finding in InspectGit(path, creation, args)) yield return finding;
        }
    }

    private static IEnumerable<RemoteStateFinding> InspectGit(
        string path, SyntaxNode node, IReadOnlyList<string?> arguments)
    {
        if (arguments.Count == 0 || arguments[0] is null)
        {
            yield return Finding(path, node, "git command", "real checkout git command is not statically known");
            yield break;
        }
        foreach (var finding in InspectGit(path,
                     node.GetLocation().GetLineSpan().StartLinePosition.Line + 1,
                     arguments[0]!, arguments.Skip(1).ToArray(), AllowedRevisions))
            yield return finding;
    }

    private static IEnumerable<RemoteStateFinding> InspectGit(
        string path, int line, string command, IReadOnlyList<string?> arguments,
        IReadOnlySet<string> allowed)
    {
        if (RemoteGitCommands.Contains(command))
        {
            yield return new(path, line, $"git {command}",
                "real checkout command contacts a repository remote");
            yield break;
        }
        if (!RevisionGitCommands.Contains(command)) yield break;
        if (RevisionOperands(arguments).Any(item => item is null || !allowed.Contains(item)))
        {
            yield return new(path, line, "disallowed revision",
                $"git {command} resolves a revision that is not head or base (HEAD or HEAD^1)");
        }
    }

    private static IEnumerable<string?> RevisionOperands(IReadOnlyList<string?> arguments)
    {
        foreach (var value in arguments)
        {
            if (value == "--") yield break;
            if (value is null || !value.StartsWith("-", StringComparison.Ordinal)) yield return value;
        }
    }

    private static bool IsAllowedRevision(ExpressionSyntax expression) =>
        TryLiteral(expression, out var value) && AllowedRevisions.Contains(value);

    private static bool UsesRealGateway(InvocationExpressionSyntax invocation, SyntaxNode scope) =>
        invocation.Expression is MemberAccessExpressionSyntax member
        && IsRealGateway(member.Expression, scope, new HashSet<string>(StringComparer.Ordinal));

    private static bool IsRealGateway(ExpressionSyntax expression, SyntaxNode scope, ISet<string> visited)
    {
        if (expression is ParenthesizedExpressionSyntax grouped)
            return IsRealGateway(grouped.Expression, scope, visited);
        if (expression is ObjectCreationExpressionSyntax creation
            && RightmostName(creation.Type) == "GitRepositoryGateway")
            return creation.ArgumentList?.Arguments.FirstOrDefault() is { } argument
                && IsRealCheckout(argument.Expression, scope);
        return expression is IdentifierNameSyntax identifier && visited.Add(identifier.Identifier.ValueText)
            && Initializers(scope, identifier.Identifier.ValueText)
                .Any(item => IsRealGateway(item, scope, visited));
    }

    private static bool IsRealCheckout(ExpressionSyntax expression, SyntaxNode scope) =>
        IsRealCheckout(expression, scope, new HashSet<string>(StringComparer.Ordinal));

    private static bool IsRealCheckout(ExpressionSyntax expression, SyntaxNode scope, ISet<string> visited)
    {
        if (expression.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
            .Any(static item => InvocationName(item) == "FindRoot"
                && item.Expression is MemberAccessExpressionSyntax member
                && RightmostName(member.Expression).EndsWith("RepositoryLayout", StringComparison.Ordinal)))
            return true;
        return expression is IdentifierNameSyntax identifier && visited.Add(identifier.Identifier.ValueText)
            && Initializers(scope, identifier.Identifier.ValueText)
                .Any(item => IsRealCheckout(item, scope, visited));
    }

    private static IEnumerable<ExpressionSyntax> Initializers(SyntaxNode scope, string identifier) =>
        scope.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Where(item => item.Identifier.ValueText == identifier && item.Initializer is not null)
            .Select(static item => item.Initializer!.Value);

    private static bool UsesHttpClient(InvocationExpressionSyntax invocation, SyntaxNode scope)
    {
        if (invocation.Expression is not MemberAccessExpressionSyntax member) return false;
        if (member.Expression is ObjectCreationExpressionSyntax creation)
            return RightmostName(creation.Type) == "HttpClient";
        return member.Expression is IdentifierNameSyntax identifier
            && scope.DescendantNodes().OfType<VariableDeclaratorSyntax>().Any(item =>
                item.Identifier.ValueText == identifier.Identifier.ValueText
                && item.Parent is VariableDeclarationSyntax declaration
                && (RightmostName(declaration.Type) == "HttpClient"
                    || item.Initializer?.Value is ObjectCreationExpressionSyntax client
                        && RightmostName(client.Type) == "HttpClient"));
    }

    private static bool TryLiteral(ExpressionSyntax expression, out string value)
    {
        if (expression is LiteralExpressionSyntax literal && literal.IsKind(SyntaxKind.StringLiteralExpression))
        {
            value = literal.Token.ValueText;
            return true;
        }
        value = string.Empty;
        return false;
    }
    private static string? LiteralOrNull(ExpressionSyntax expression) =>
        TryLiteral(expression, out var value) ? value : null;

    private static bool TryStrings(ExpressionSyntax expression, out IReadOnlyList<string?> values)
    {
        IEnumerable<ExpressionSyntax>? elements = expression switch
        {
            CollectionExpressionSyntax items => items.Elements.OfType<ExpressionElementSyntax>()
                .Select(static item => item.Expression),
            ArrayCreationExpressionSyntax array => array.Initializer?.Expressions,
            ImplicitArrayCreationExpressionSyntax array => array.Initializer.Expressions,
            _ => null,
        };
        values = elements?.Select(LiteralOrNull).ToArray() ?? [];
        return elements is not null;
    }

    private static bool IsRepositoryApiUrl(string value) => Uri.TryCreate(value, UriKind.Absolute, out var uri)
        && (string.Equals(uri.Host, "api.github.com", StringComparison.OrdinalIgnoreCase)
            || string.Equals(uri.Host, "gitlab.com", StringComparison.OrdinalIgnoreCase)
                && uri.AbsolutePath.StartsWith("/api/", StringComparison.Ordinal)
            || uri.Host.EndsWith(".github.com", StringComparison.OrdinalIgnoreCase)
                && uri.AbsolutePath.StartsWith("/api/", StringComparison.Ordinal));
    private static bool IsExecutable(string value, string executable) =>
        string.Equals(value, executable, StringComparison.Ordinal)
        || value.EndsWith('/' + executable, StringComparison.Ordinal);
    private static string InvocationName(InvocationExpressionSyntax invocation) => invocation.Expression switch
    {
        IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
        GenericNameSyntax generic => generic.Identifier.ValueText,
        MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
        _ => string.Empty,
    };
    private static SyntaxNode Scope(SyntaxNode node, SyntaxNode root) =>
        node.FirstAncestorOrSelf<BaseMethodDeclarationSyntax>() ?? root;
    private static string RightmostName(SyntaxNode node) => node switch
    {
        IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
        QualifiedNameSyntax qualified => qualified.Right.Identifier.ValueText,
        AliasQualifiedNameSyntax alias => alias.Name.Identifier.ValueText,
        MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
        _ => string.Empty,
    };
    private static bool IsMember(ExpressionSyntax expression, string receiver, string member) =>
        expression is MemberAccessExpressionSyntax access && access.Name.Identifier.ValueText == member
        && access.Expression is IdentifierNameSyntax identifier && identifier.Identifier.ValueText == receiver;
    private static RemoteStateFinding Finding(string path, SyntaxNode node, string operation, string message) =>
        new(path, node.GetLocation().GetLineSpan().StartLinePosition.Line + 1, operation, message);

}
