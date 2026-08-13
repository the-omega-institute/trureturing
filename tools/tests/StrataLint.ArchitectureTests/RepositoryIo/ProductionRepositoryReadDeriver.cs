using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

internal sealed record RepositoryReadSource(string Assembly, string Path, string Content);
internal sealed record IndirectRepositoryReadSite(string Path, int Line, string ReaderType)
{
    internal string Location => $"{Path}:{Line}";
}

internal static class ProductionRepositoryReadDeriver
{
    private const string ScribeTestsPrefix = "tools/tests/StrataLint.Scribe.Tests/";

    internal static IReadOnlySet<string> DeriveRepositoryReaderTypes(string repositoryRoot) =>
        DeriveReaderTypes(ProductionSources(repositoryRoot));

    internal static IReadOnlySet<string> DeriveReaderTypes(
        IEnumerable<RepositoryReadSource> sourceFiles) => Analyze(sourceFiles).Readers;

    private static RepositoryReadAnalysis Analyze(
        IEnumerable<RepositoryReadSource> sourceFiles)
    {
        var sources = sourceFiles.Select(Parse).ToArray();
        var repositoryTypes = sources
            .SelectMany(static source => source.Types)
            .Select(static type => type.Identifier.ValueText)
            .ToHashSet(StringComparer.Ordinal);
        var internalTypes = sources
            .SelectMany(static source => source.Types)
            .Where(static type => !type.Modifiers.Any(SyntaxKind.PublicKeyword))
            .Select(static type => type.Identifier.ValueText)
            .ToHashSet(StringComparer.Ordinal);
        var readers = new HashSet<string>(StringComparer.Ordinal);
        var directReaders = new HashSet<string>(StringComparer.Ordinal);
        var calls = new Dictionary<string, HashSet<string>>(StringComparer.Ordinal);

        foreach (var source in sources)
        {
            var directLines = RepositoryIoAccessPolicy.InspectSource(source.Source.Path, source.Source.Content)
                .Select(static finding => FindingLine(finding.Message))
                .Where(static line => line is not null)
                .Select(static line => line!.Value)
                .ToHashSet();

            foreach (var type in source.Types)
            {
                var typeName = type.Identifier.ValueText;
                var span = type.GetLocation().GetLineSpan();
                if (directLines.Any(line => line >= span.StartLinePosition.Line + 1
                        && line <= span.EndLinePosition.Line + 1))
                {
                    readers.Add(typeName);
                    directReaders.Add(typeName);
                }

                var outgoing = calls.GetValueOrDefault(typeName);
                if (outgoing is null)
                {
                    outgoing = new HashSet<string>(StringComparer.Ordinal);
                    calls.Add(typeName, outgoing);
                }

                foreach (var callable in type.Members.OfType<BaseMethodDeclarationSyntax>())
                {
                    ClassifyCalls(callable, repositoryTypes, outgoing, readers, directReaders, typeName);
                }
            }
        }

        bool changed;
        do
        {
            changed = false;
            foreach (var (caller, callees) in calls)
            {
                if (!readers.Contains(caller) && callees.Any(readers.Contains))
                {
                    changed |= readers.Add(caller);
                }
            }
        }
        while (changed);

        return new RepositoryReadAnalysis(readers, directReaders, internalTypes);
    }

    internal static IReadOnlyList<IndirectRepositoryReadSite> InspectScribeTests(
        string repositoryRoot)
    {
        var analysis = Analyze(ProductionSources(repositoryRoot));
        return GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => file.RelativePath.StartsWith(ScribeTestsPrefix, StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .SelectMany(file => InspectTestSource(
                file.RelativePath,
                File.ReadAllText(file.FullPath),
                analysis.Readers.Where(analysis.InternalTypes.Contains)
                    .ToHashSet(StringComparer.Ordinal)))
            .OrderBy(static site => site.Path, StringComparer.Ordinal)
            .ThenBy(static site => site.Line)
            .ToArray();
    }

    internal static IReadOnlyList<string> FindAddedSites(
        IEnumerable<string> current,
        IReadOnlySet<string> baseline) => current
        .Except(baseline, StringComparer.Ordinal)
        .Order(StringComparer.Ordinal)
        .ToArray();

    private static IEnumerable<RepositoryReadSource> ProductionSources(string repositoryRoot) =>
        GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => file.RelativePath.StartsWith("tools/StrataLint.", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                && !file.RelativePath.Contains(".Tests/", StringComparison.Ordinal))
            .Select(file => new RepositoryReadSource(
                ProjectName(file.RelativePath),
                file.RelativePath,
                File.ReadAllText(file.FullPath)));

    private static ParsedSource Parse(RepositoryReadSource source)
    {
        var root = CSharpSyntaxTree.ParseText(source.Content).GetRoot();
        return new ParsedSource(
            source,
            root.DescendantNodes().OfType<TypeDeclarationSyntax>().ToArray());
    }

    private static void ClassifyCalls(
        BaseMethodDeclarationSyntax callable,
        IReadOnlySet<string> repositoryTypes,
        HashSet<string> outgoing,
        HashSet<string> readers,
        HashSet<string> directReaders,
        string caller)
    {
        var pathParameters = callable.ParameterList.Parameters
            .Where(IsPathParameter)
            .Select(static parameter => parameter.Identifier.ValueText)
            .ToHashSet(StringComparer.Ordinal);
        var variableTypes = callable.DescendantNodes().OfType<VariableDeclarationSyntax>()
            .SelectMany(static declaration => declaration.Variables.Select(variable =>
                (variable.Identifier.ValueText, Type: RightmostName(declaration.Type))))
            .Concat(callable.ParameterList.Parameters.Select(static parameter =>
                (parameter.Identifier.ValueText, Type: RightmostName(parameter.Type))))
            .GroupBy(static item => item.ValueText, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => group.Last().Type,
                StringComparer.Ordinal);

        foreach (var invocation in callable.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            var owner = CalledType(invocation, variableTypes, caller);
            if (owner is not null && repositoryTypes.Contains(owner))
            {
                outgoing.Add(owner);
                continue;
            }

            if (pathParameters.Count != 0
                && invocation.ArgumentList.Arguments.Any(argument =>
                    argument.Expression.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
                        .Any(identifier => pathParameters.Contains(identifier.Identifier.ValueText))))
            {
                readers.Add(caller);
                directReaders.Add(caller);
            }
        }
    }

    private static IReadOnlyList<IndirectRepositoryReadSite> InspectTestSource(
        string path,
        string content,
        IReadOnlySet<string> readers)
    {
        var root = CSharpSyntaxTree.ParseText(content).GetRoot();
        var repositoryVariables = root.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Where(static variable => variable.Initializer?.Value
                .DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
                .Any(IsRepositoryDiscovery) is true)
            .Select(static variable => variable.Identifier.ValueText)
            .ToHashSet(StringComparer.Ordinal);

        return root.DescendantNodes().OfType<InvocationExpressionSyntax>()
            .Select(invocation => (Invocation: invocation, Reader: CalledType(invocation, null, null)))
            .Where(item => item.Reader is not null && readers.Contains(item.Reader))
            .Where(item => item.Invocation.ArgumentList.Arguments.Any(argument =>
                IsRepositoryRoot(argument.Expression, repositoryVariables)))
            .Select(item => new IndirectRepositoryReadSite(
                path,
                item.Invocation.GetLocation().GetLineSpan().StartLinePosition.Line + 1,
                item.Reader!))
            .ToArray();
    }

    private static bool IsRepositoryRoot(
        ExpressionSyntax expression,
        IReadOnlySet<string> repositoryVariables) =>
        expression.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
            .Any(IsRepositoryDiscovery)
        || expression.DescendantNodesAndSelf().OfType<MemberAccessExpressionSyntax>().Any(member =>
            member.Name.Identifier.ValueText == "FullPath"
            && member.Expression is MemberAccessExpressionSyntax root
            && root.Name.Identifier.ValueText == "Root"
            && root.Expression is IdentifierNameSyntax identifier
            && repositoryVariables.Contains(identifier.Identifier.ValueText));

    private static bool IsRepositoryDiscovery(InvocationExpressionSyntax invocation) =>
        invocation.Expression is MemberAccessExpressionSyntax member
        && member.Name.Identifier.ValueText == "Discover"
        && RightmostName(member.Expression) == "RepositoryAccessor";

    private static bool IsPathParameter(ParameterSyntax parameter)
    {
        var type = RightmostName(parameter.Type);
        if (type is "FileInfo" or "DirectoryInfo" or "Uri")
        {
            return true;
        }

        var name = parameter.Identifier.ValueText;
        return type == "string"
            && (name.Contains("path", StringComparison.OrdinalIgnoreCase)
                || name.Contains("root", StringComparison.OrdinalIgnoreCase)
                || name.Contains("directory", StringComparison.OrdinalIgnoreCase)
                || name.Contains("file", StringComparison.OrdinalIgnoreCase)
                || name.Contains("uri", StringComparison.OrdinalIgnoreCase));
    }

    private static string? CalledType(
        InvocationExpressionSyntax invocation,
        IReadOnlyDictionary<string, string>? variableTypes,
        string? containingType)
    {
        if (invocation.Expression is IdentifierNameSyntax)
        {
            return containingType;
        }

        if (invocation.Expression is not MemberAccessExpressionSyntax member)
        {
            return null;
        }

        if (member.Expression is IdentifierNameSyntax identifier
            && variableTypes is not null
            && variableTypes.TryGetValue(identifier.Identifier.ValueText, out var variableType))
        {
            return variableType;
        }

        return RightmostName(member.Expression);
    }

    private static int? FindingLine(string message)
    {
        const string prefix = "line ";
        if (!message.StartsWith(prefix, StringComparison.Ordinal))
        {
            return null;
        }

        var colon = message.IndexOf(':', prefix.Length);
        return colon > prefix.Length
            && int.TryParse(message.AsSpan(prefix.Length, colon - prefix.Length), out var line)
                ? line
                : null;
    }

    private static string ProjectName(string path)
    {
        var slash = path.IndexOf('/', "tools/".Length);
        return path["tools/".Length..slash];
    }

    private static string RightmostName(SyntaxNode? node) => node switch
    {
        IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
        GenericNameSyntax generic => generic.Identifier.ValueText,
        QualifiedNameSyntax qualified => qualified.Right.Identifier.ValueText,
        AliasQualifiedNameSyntax alias => alias.Name.Identifier.ValueText,
        MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
        PredefinedTypeSyntax predefined => predefined.Keyword.ValueText,
        _ => string.Empty,
    };

    private sealed record ParsedSource(
        RepositoryReadSource Source,
        IReadOnlyList<TypeDeclarationSyntax> Types);

    private sealed record RepositoryReadAnalysis(
        IReadOnlySet<string> Readers,
        IReadOnlySet<string> DirectReaders,
        IReadOnlySet<string> InternalTypes);
}
