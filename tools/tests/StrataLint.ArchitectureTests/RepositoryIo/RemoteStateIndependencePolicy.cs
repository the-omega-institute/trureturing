using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using StrataLint.Engine;
using System.Text;
using System.Text.RegularExpressions;
using YamlDotNet.Core;
using YamlDotNet.RepresentationModel;

namespace StrataLint.ArchitectureTests;

internal sealed record RemoteStateSource(string Path, string Content);

internal sealed record RemoteStateFinding(
    string Path,
    int Line,
    string Operation,
    string Message)
{
    internal string Location => $"{Path}:{Line}";

    public override string ToString() => $"{Location}: {Operation}: {Message}";
}

internal static partial class RemoteStateIndependencePolicy
{
    private static readonly IReadOnlySet<string> RevisionReaders =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "ReadRevision",
            "ReadRevisionFile",
        };

    private static readonly IReadOnlySet<string> FetchingGitCommands =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "fetch",
            "ls-remote",
            "pull",
        };

    private static readonly IReadOnlySet<string> RemoteApiCommands =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "api",
            "issue",
            "pr",
            "release",
            "repo",
            "run",
            "search",
            "workflow",
        };

    private static readonly IReadOnlySet<string> RevisionResolvingGitCommands =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "branch",
            "cat-file",
            "checkout",
            "diff",
            "log",
            "ls-tree",
            "merge-base",
            "reset",
            "rev-parse",
            "show",
            "switch",
        };

    private static readonly IReadOnlySet<string> GitOptionsWithValues =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "-C",
            "-c",
            "--config-env",
            "--exec-path",
            "--git-dir",
            "--namespace",
            "--super-prefix",
            "--work-tree",
        };

    internal static IReadOnlyList<RemoteStateFinding> InspectRepository(string repositoryRoot)
    {
        var findings = new List<RemoteStateFinding>();
        foreach (var file in GitIndexRepositoryFiles.Enumerate(repositoryRoot))
        {
            if (file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            {
                findings.AddRange(InspectTestSource(new RemoteStateSource(
                    file.RelativePath,
                    File.ReadAllText(file.FullPath))));
            }
            else if (file.RelativePath.StartsWith(".github/workflows/", StringComparison.Ordinal)
                     && (file.RelativePath.EndsWith(".yml", StringComparison.Ordinal)
                         || file.RelativePath.EndsWith(".yaml", StringComparison.Ordinal)))
            {
                findings.AddRange(InspectWorkflowSource(new RemoteStateSource(
                    file.RelativePath,
                    File.ReadAllText(file.FullPath))));
            }
        }

        return findings
            .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Line)
            .ThenBy(static finding => finding.Operation, StringComparer.Ordinal)
            .ToArray();
    }

    internal static IReadOnlyList<RemoteStateFinding> InspectTestSource(RemoteStateSource source)
    {
        var tree = CSharpSyntaxTree.ParseText(source.Content);
        var root = tree.GetRoot();
        var findings = tree.GetDiagnostics()
            .Where(static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error)
            .Select(diagnostic => new RemoteStateFinding(
                source.Path,
                diagnostic.Location.GetLineSpan().StartLinePosition.Line + 1,
                "unrecognized C#",
                diagnostic.GetMessage()))
            .ToList();
        foreach (var invocation in root.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            var scope = AnalysisScope(invocation, root);
            var constants = DeriveStringConstants(scope);
            var realRoots = DeriveRealRepositoryVariables(scope);
            var realGateways = DeriveRealGatewayVariables(scope, realRoots);
            var method = InvocationName(invocation);
            findings.AddRange(InspectProcessInvocation(
                source.Path,
                invocation,
                constants,
                realRoots));
            if (RevisionReaders.Contains(method)
                && UsesRealGateway(invocation, realRoots, realGateways))
            {
                var revision = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression;
                if (revision is null
                    || !TryConstantString(revision, constants, out var value)
                    || !IsProvenRemoteIndependentRevision(value))
                {
                    findings.Add(Finding(
                        source.Path,
                        invocation,
                        "remote revision",
                        revision is not null && TryConstantString(revision, constants, out value)
                            ? $"real repository resolves remote-tracking or ambiguous revision '{value}'"
                            : "real repository revision is not provably local or content-addressed"));
                }
            }

            if (method == "InspectAdmissionTopology"
                && UsesRealGateway(invocation, realRoots, realGateways))
            {
                findings.Add(Finding(
                    source.Path,
                    invocation,
                    "remote API",
                    "real repository topology inspection calls git ls-remote"));
            }

            if (method == "RunGit"
                && invocation.ArgumentList.Arguments.Count >= 2
                && DependsOnRealRepository(
                    invocation.ArgumentList.Arguments[0].Expression,
                    realRoots))
            {
                var arguments = invocation.ArgumentList.Arguments.Skip(1)
                    .Select(static argument => argument.Expression)
                    .Select(expression => TryConstantString(expression, constants, out var value)
                        ? value
                        : null)
                    .ToArray();
                findings.AddRange(InspectGitArguments(source.Path, invocation, arguments));
            }
        }

        findings.AddRange(InspectProcessStartInfos(source.Path, root));

        return findings;
    }

    internal static IReadOnlyList<RemoteStateFinding> InspectWorkflowSource(RemoteStateSource source)
    {
        var stream = new YamlStream();
        try
        {
            stream.Load(new StringReader(source.Content));
        }
        catch (YamlException exception)
        {
            return
            [
                new RemoteStateFinding(
                    source.Path,
                    checked((int)exception.Start.Line + 1),
                    "unrecognized workflow",
                    exception.Message),
            ];
        }

        if (stream.Documents.Count != 1
            || stream.Documents[0].RootNode is not YamlMappingNode root
            || !TryMapping(root, "jobs", out var jobs))
        {
            return
            [
                new RemoteStateFinding(
                    source.Path,
                    1,
                    "unrecognized workflow",
                    "workflow must contain one jobs mapping"),
            ];
        }

        var findings = new List<RemoteStateFinding>();
        foreach (var job in jobs.Children.Values.OfType<YamlMappingNode>())
        {
            if (!TrySequence(job, "steps", out var steps))
            {
                continue;
            }

            var checkoutSeen = false;
            foreach (var step in steps.Children.OfType<YamlMappingNode>())
            {
                if (TryScalar(step, "uses", out var uses)
                    && uses.Value?.StartsWith("actions/checkout@", StringComparison.Ordinal) is true)
                {
                    checkoutSeen = true;
                    continue;
                }

                if (!checkoutSeen)
                {
                    continue;
                }

                if (TryScalar(step, "uses", out uses)
                    && uses.Value?.StartsWith("actions/github-script@", StringComparison.Ordinal) is true)
                {
                    findings.Add(new RemoteStateFinding(
                        source.Path,
                        checked((int)uses.Start.Line + 1),
                        "remote API",
                        "post-checkout github-script may query live repository state"));
                }

                if (TryScalar(step, "run", out var run))
                {
                    findings.AddRange(InspectShell(
                        source.Path,
                        run.Value ?? string.Empty,
                        WorkflowScalarFirstLine(run)));
                }
            }
        }

        return findings;
    }

    private static IReadOnlyDictionary<string, string> DeriveStringConstants(SyntaxNode root)
    {
        var constants = new Dictionary<string, string>(StringComparer.Ordinal);
        bool changed;
        do
        {
            changed = false;
            foreach (var variable in root.DescendantNodes().OfType<VariableDeclaratorSyntax>())
            {
                if (!constants.ContainsKey(variable.Identifier.ValueText)
                    && variable.Initializer is not null
                    && TryConstantString(variable.Initializer.Value, constants, out var value))
                {
                    constants.Add(variable.Identifier.ValueText, value);
                    changed = true;
                }
            }
        }
        while (changed);
        return constants;
    }

    private static IReadOnlySet<string> DeriveRealRepositoryVariables(SyntaxNode root)
    {
        var variables = new HashSet<string>(StringComparer.Ordinal);
        bool changed;
        do
        {
            changed = false;
            foreach (var variable in root.DescendantNodes().OfType<VariableDeclaratorSyntax>())
            {
                if (variable.Initializer is not null
                    && DependsOnRealRepository(variable.Initializer.Value, variables))
                {
                    changed |= variables.Add(variable.Identifier.ValueText);
                }
            }

            foreach (var assignment in root.DescendantNodes().OfType<AssignmentExpressionSyntax>())
            {
                if (assignment.Left is IdentifierNameSyntax identifier
                    && DependsOnRealRepository(assignment.Right, variables))
                {
                    changed |= variables.Add(identifier.Identifier.ValueText);
                }
            }
        }
        while (changed);
        return variables;
    }

    private static IReadOnlySet<string> DeriveRealGatewayVariables(
        SyntaxNode root,
        IReadOnlySet<string> realRoots)
    {
        var variables = new HashSet<string>(StringComparer.Ordinal);
        bool changed;
        do
        {
            changed = false;
            foreach (var variable in root.DescendantNodes().OfType<VariableDeclaratorSyntax>())
            {
                if (variable.Initializer is not null
                    && IsRealGatewayExpression(variable.Initializer.Value, realRoots, variables))
                {
                    changed |= variables.Add(variable.Identifier.ValueText);
                }
            }
        }
        while (changed);
        return variables;
    }

    private static bool DependsOnRealRepository(
        ExpressionSyntax expression,
        IReadOnlySet<string> realRoots) =>
        expression.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
            .Any(static invocation =>
                InvocationName(invocation) == "FindRoot"
                && invocation.Expression is MemberAccessExpressionSyntax member
                && RightmostName(member.Expression).EndsWith("RepositoryLayout", StringComparison.Ordinal))
        || expression.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
            .Any(identifier => realRoots.Contains(identifier.Identifier.ValueText));

    private static bool UsesRealGateway(
        InvocationExpressionSyntax invocation,
        IReadOnlySet<string> realRoots,
        IReadOnlySet<string> realGateways) =>
        invocation.Expression is MemberAccessExpressionSyntax member
        && IsRealGatewayExpression(member.Expression, realRoots, realGateways);

    private static bool IsRealGatewayExpression(
        ExpressionSyntax expression,
        IReadOnlySet<string> realRoots,
        IReadOnlySet<string> realGateways) => expression switch
    {
        IdentifierNameSyntax identifier => realGateways.Contains(identifier.Identifier.ValueText),
        ParenthesizedExpressionSyntax parenthesized =>
            IsRealGatewayExpression(parenthesized.Expression, realRoots, realGateways),
        ObjectCreationExpressionSyntax creation
            when RightmostName(creation.Type) == "GitRepositoryGateway" =>
            creation.ArgumentList?.Arguments.FirstOrDefault() is { } argument
            && DependsOnRealRepository(argument.Expression, realRoots),
        _ => false,
    };

    private static bool TryConstantString(
        ExpressionSyntax expression,
        IReadOnlyDictionary<string, string> constants,
        out string value)
    {
        switch (expression)
        {
            case LiteralExpressionSyntax literal when literal.IsKind(SyntaxKind.StringLiteralExpression):
                value = literal.Token.ValueText;
                return true;
            case IdentifierNameSyntax identifier
                when constants.TryGetValue(identifier.Identifier.ValueText, out var constant):
                value = constant;
                return true;
            case ParenthesizedExpressionSyntax parenthesized:
                return TryConstantString(parenthesized.Expression, constants, out value);
            case BinaryExpressionSyntax binary when binary.IsKind(SyntaxKind.AddExpression)
                && TryConstantString(binary.Left, constants, out var left)
                && TryConstantString(binary.Right, constants, out var right):
                value = left + right;
                return true;
            default:
                value = string.Empty;
                return false;
        }
    }

    private static bool IsProvenRemoteIndependentRevision(string revision) =>
        GitObjectId().IsMatch(revision)
        || HeadRevision().IsMatch(revision)
        || revision.StartsWith("refs/heads/", StringComparison.Ordinal)
        || revision.StartsWith("refs/tags/", StringComparison.Ordinal)
        || revision.StartsWith("heads/", StringComparison.Ordinal)
        || revision.StartsWith("tags/", StringComparison.Ordinal);

    private static IEnumerable<RemoteStateFinding> InspectGitArguments(
        string path,
        SyntaxNode invocation,
        IReadOnlyList<string?> arguments)
    {
        if (arguments.Count == 0 || arguments[0] is null)
        {
            yield break;
        }

        var command = arguments[0]!;
        if (FetchingGitCommands.Contains(command))
        {
            yield return Finding(path, invocation, $"git {command}",
                "real repository command contacts a remote");
            yield break;
        }

        if (RevisionResolvingGitCommands.Contains(command)
            && arguments.Skip(1).TakeWhile(static argument => argument != "--")
                .OfType<string>().Any(IsRemoteTrackingRevision))
        {
            yield return Finding(path, invocation, "remote revision",
                "real repository git command resolves a remote-tracking revision");
        }
    }

    private static IReadOnlyList<RemoteStateFinding> InspectShell(
        string path,
        string script,
        int firstLine)
    {
        var tokens = TokenizeShell(script);
        var findings = new List<RemoteStateFinding>();
        for (var index = 0; index < tokens.Count; index++)
        {
            if (tokens[index].IsBoundary)
            {
                continue;
            }

            if (IsExecutable(tokens[index].Value, "git"))
            {
                var commandIndex = GitCommandIndex(tokens, index);
                if (commandIndex is null)
                {
                    continue;
                }

                var command = tokens[commandIndex.Value].Value;
                if (FetchingGitCommands.Contains(command)
                    || command == "remote" && NextValue(tokens, commandIndex.Value) == "update"
                    || command == "submodule" && NextValue(tokens, commandIndex.Value) == "update"
                        && !CommandValues(tokens, commandIndex.Value).Contains("--no-fetch", StringComparer.Ordinal))
                {
                    findings.Add(new RemoteStateFinding(
                        path,
                        firstLine + tokens[index].Line - 1,
                        $"git {command}",
                        "post-checkout command may contact a repository remote"));
                    continue;
                }

                if (RevisionResolvingGitCommands.Contains(command)
                    && GitRevisionValues(tokens, commandIndex.Value)
                        .Any(IsRemoteTrackingRevision))
                {
                    findings.Add(new RemoteStateFinding(
                        path,
                        firstLine + tokens[index].Line - 1,
                        "remote revision",
                        "post-checkout git command resolves a remote-tracking revision"));
                }
            }
            else if (IsExecutable(tokens[index].Value, "gh")
                     && RemoteApiCommands.Contains(NextValue(tokens, index) ?? string.Empty))
            {
                findings.Add(new RemoteStateFinding(
                    path,
                    firstLine + tokens[index].Line - 1,
                    "remote API",
                    "post-checkout GitHub CLI command queries live repository state"));
            }
            else if ((IsExecutable(tokens[index].Value, "curl")
                      || IsExecutable(tokens[index].Value, "wget"))
                     && CommandValues(tokens, index).Any(IsRepositoryApiUrl))
            {
                findings.Add(new RemoteStateFinding(
                    path,
                    firstLine + tokens[index].Line - 1,
                    "remote API",
                    "post-checkout command queries a live repository API"));
            }
        }

        return findings;
    }

    private static int? GitCommandIndex(IReadOnlyList<ShellToken> tokens, int gitIndex)
    {
        for (var index = gitIndex + 1; index < tokens.Count && !tokens[index].IsBoundary; index++)
        {
            var value = tokens[index].Value;
            if (GitOptionsWithValues.Contains(value))
            {
                index++;
                continue;
            }

            if (value.StartsWith("-", StringComparison.Ordinal))
            {
                continue;
            }

            return index;
        }

        return null;
    }

    private static string? NextValue(IReadOnlyList<ShellToken> tokens, int index) =>
        index + 1 < tokens.Count && !tokens[index + 1].IsBoundary
            ? tokens[index + 1].Value
            : null;

    private static IReadOnlyList<string> CommandValues(
        IReadOnlyList<ShellToken> tokens,
        int start)
    {
        var values = new List<string>();
        for (var index = start + 1; index < tokens.Count && !tokens[index].IsBoundary; index++)
        {
            values.Add(tokens[index].Value);
        }
        return values;
    }

    private static IEnumerable<string> GitRevisionValues(
        IReadOnlyList<ShellToken> tokens,
        int commandIndex)
    {
        for (var index = commandIndex + 1;
             index < tokens.Count && !tokens[index].IsBoundary;
             index++)
        {
            var value = tokens[index].Value;
            if (value == "--")
            {
                yield break;
            }
            if (!value.StartsWith("-", StringComparison.Ordinal))
            {
                yield return value;
            }
        }
    }

    private static IReadOnlyList<ShellToken> TokenizeShell(string script)
    {
        var tokens = new List<ShellToken>();
        var value = new StringBuilder();
        var line = 1;
        var tokenLine = line;
        char quote = '\0';

        void Flush()
        {
            if (value.Length == 0)
            {
                return;
            }
            tokens.Add(new ShellToken(value.ToString(), tokenLine, false));
            value.Clear();
        }

        void Boundary()
        {
            Flush();
            if (tokens.Count == 0 || !tokens[^1].IsBoundary)
            {
                tokens.Add(new ShellToken(string.Empty, line, true));
            }
        }

        for (var index = 0; index < script.Length; index++)
        {
            var current = script[index];
            if (current == '\\' && index + 1 < script.Length)
            {
                if (script[index + 1] == '\n')
                {
                    line++;
                    index++;
                    continue;
                }
                if (value.Length == 0) tokenLine = line;
                value.Append(script[++index]);
                continue;
            }

            if (quote != '\'' && current == '$' && index + 1 < script.Length
                && script[index + 1] == '(')
            {
                Boundary();
                index++;
                continue;
            }

            if (quote == '\0' && current is '\'' or '"')
            {
                if (value.Length == 0) tokenLine = line;
                quote = current;
                continue;
            }
            if (quote != '\0' && current == quote)
            {
                quote = '\0';
                continue;
            }

            if (quote == '\0' && current == '#'
                && (index == 0 || char.IsWhiteSpace(script[index - 1])))
            {
                Flush();
                while (index < script.Length && script[index] != '\n') index++;
                if (index < script.Length)
                {
                    Boundary();
                    line++;
                }
                continue;
            }

            if (quote == '\0' && current == '\n')
            {
                Boundary();
                line++;
                continue;
            }
            if (quote == '\0' && (char.IsWhiteSpace(current) || current is ';' or '|' or '&' or '(' or ')'))
            {
                if (current is ';' or '|' or '&' or '(' or ')') Boundary();
                else Flush();
                continue;
            }

            if (value.Length == 0) tokenLine = line;
            value.Append(current);
        }
        Flush();
        return tokens;
    }

    private static bool IsRemoteTrackingRevision(string value)
    {
        var revision = value.Trim('"', '\'');
        if (revision.StartsWith("refs/remotes/", StringComparison.Ordinal)
            || revision.StartsWith("remotes/", StringComparison.Ordinal))
        {
            return true;
        }

        if (revision.StartsWith("refs/heads/", StringComparison.Ordinal)
            || revision.StartsWith("refs/tags/", StringComparison.Ordinal)
            || revision.StartsWith("heads/", StringComparison.Ordinal)
            || revision.StartsWith("tags/", StringComparison.Ordinal)
            || revision.StartsWith("./", StringComparison.Ordinal)
            || revision.StartsWith("../", StringComparison.Ordinal)
            || revision.Contains("${{", StringComparison.Ordinal)
            || revision.StartsWith('$'))
        {
            return false;
        }

        return revision.Contains('/', StringComparison.Ordinal)
            && !Uri.TryCreate(revision, UriKind.Absolute, out _);
    }

    private static bool IsRepositoryApiUrl(string value) =>
        Uri.TryCreate(value, UriKind.Absolute, out var uri)
        && (string.Equals(uri.Host, "api.github.com", StringComparison.OrdinalIgnoreCase)
            || string.Equals(uri.Host, "gitlab.com", StringComparison.OrdinalIgnoreCase)
                && uri.AbsolutePath.StartsWith("/api/", StringComparison.Ordinal)
            || uri.Host.EndsWith(".github.com", StringComparison.OrdinalIgnoreCase)
                && uri.AbsolutePath.StartsWith("/api/", StringComparison.Ordinal));

    private static bool IsExecutable(string value, string executable) =>
        string.Equals(value, executable, StringComparison.Ordinal)
        || value.EndsWith('/' + executable, StringComparison.Ordinal);

    private static string InvocationName(InvocationExpressionSyntax invocation) =>
        invocation.Expression switch
        {
            IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
            GenericNameSyntax generic => generic.Identifier.ValueText,
            MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
            _ => string.Empty,
        };

    private static SyntaxNode AnalysisScope(SyntaxNode node, SyntaxNode root) =>
        node.FirstAncestorOrSelf<BaseMethodDeclarationSyntax>() ?? root;

    private static string RightmostName(SyntaxNode node) => node switch
    {
        IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
        QualifiedNameSyntax qualified => qualified.Right.Identifier.ValueText,
        AliasQualifiedNameSyntax alias => alias.Name.Identifier.ValueText,
        MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
        _ => string.Empty,
    };

    private static RemoteStateFinding Finding(
        string path,
        SyntaxNode node,
        string operation,
        string message) => new(
            path,
            node.GetLocation().GetLineSpan().StartLinePosition.Line + 1,
            operation,
            message);

    private static bool TryMapping(
        YamlMappingNode parent,
        string key,
        out YamlMappingNode mapping)
    {
        if (parent.Children.TryGetValue(new YamlScalarNode(key), out var node)
            && node is YamlMappingNode value)
        {
            mapping = value;
            return true;
        }
        mapping = null!;
        return false;
    }

    private static bool TrySequence(
        YamlMappingNode parent,
        string key,
        out YamlSequenceNode sequence)
    {
        if (parent.Children.TryGetValue(new YamlScalarNode(key), out var node)
            && node is YamlSequenceNode value)
        {
            sequence = value;
            return true;
        }
        sequence = null!;
        return false;
    }

    private static bool TryScalar(
        YamlMappingNode parent,
        string key,
        out YamlScalarNode scalar)
    {
        if (parent.Children.TryGetValue(new YamlScalarNode(key), out var node)
            && node is YamlScalarNode value)
        {
            scalar = value;
            return true;
        }
        scalar = null!;
        return false;
    }

    private static int WorkflowScalarFirstLine(YamlScalarNode scalar) =>
        checked((int)scalar.Start.Line
            + (scalar.Style is YamlDotNet.Core.ScalarStyle.Literal
                or YamlDotNet.Core.ScalarStyle.Folded ? 1 : 0));

    private sealed record ShellToken(string Value, int Line, bool IsBoundary);

    [GeneratedRegex("^[0-9a-fA-F]{40}(?:[0-9a-fA-F]{24})?$")]
    private static partial Regex GitObjectId();

    [GeneratedRegex("^HEAD(?:(?:\\^|~)[0-9]*|\\^\\{(?:commit|tree)\\})*$", RegexOptions.CultureInvariant)]
    private static partial Regex HeadRevision();
}
