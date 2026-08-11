using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

internal sealed record RepositoryIoAccessFinding(string Path, string Api, string Message);

internal static class RepositoryIoAccessPolicy
{
    internal const string ScribeTestsProject = "StrataLint.Scribe.Tests";
    internal const string ScribeTestsPrefix = "Meta/StrataLint/StrataLint.Scribe.Tests/";

    private static readonly IReadOnlySet<string> AuthorizedGatewayPaths =
        new HashSet<string>(StringComparer.Ordinal)
        {
            ScribeTestsPrefix + "Support/RepositoryAccessor.cs",
            ScribeTestsPrefix + "Support/TemporaryFileSystem.cs",
        };

    // These named project exemptions shrink one migration slice at a time. Only after
    // this list is empty may repository-I/O based test selection be considered.
    internal static readonly IReadOnlySet<string> DeferredProjectExemptions =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "StrataLint.Tests",
            "StrataLint.ArchitectureTests",
        };

    internal static IReadOnlyList<RepositoryIoAccessFinding> InspectRepository(
        string repositoryRoot) => GitIndexRepositoryFiles.Enumerate(repositoryRoot)
        .Where(file => file.RelativePath.StartsWith(ScribeTestsPrefix, StringComparison.Ordinal)
            && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
            && !AuthorizedGatewayPaths.Contains(file.RelativePath))
        .SelectMany(file => InspectSource(file.RelativePath, File.ReadAllText(file.FullPath)))
        .ToArray();

    internal static IReadOnlyList<RepositoryIoAccessFinding> InspectSource(
        string path,
        string source)
    {
        var tree = CSharpSyntaxTree.ParseText(source);
        var root = tree.GetRoot();
        var findings = tree.GetDiagnostics()
            .Where(static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error)
            .Select(diagnostic => new RepositoryIoAccessFinding(
                path,
                "UNRECOGNIZED",
                $"unrecognized C# syntax: {diagnostic.GetMessage()}"))
            .ToList();

        foreach (var alias in root.DescendantNodes().OfType<UsingDirectiveSyntax>()
                     .Where(static directive => directive.Alias is not null
                         && directive.Name?.ToString() is "System.IO.File"
                             or "System.IO.Directory"
                             or "System.IO.FileStream"
                             or "System.AppContext"))
        {
            findings.Add(new RepositoryIoAccessFinding(
                path,
                "UNRECOGNIZED",
                $"line {alias.GetLocation().GetLineSpan().StartLinePosition.Line + 1}: aliases for repository I/O APIs are not recognized"));
        }

        foreach (var invocation in root.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            if (invocation.Expression is MemberAccessExpressionSyntax member
                && TryForbiddenStaticApi(member, out var api))
            {
                findings.Add(Finding(path, api, invocation.GetLocation().GetLineSpan().StartLinePosition.Line + 1));
            }
        }

        foreach (var creation in root.DescendantNodes().OfType<ObjectCreationExpressionSyntax>())
        {
            if (RightmostName(creation.Type) == "FileStream")
            {
                findings.Add(Finding(path, "System.IO.FileStream", creation.GetLocation().GetLineSpan().StartLinePosition.Line + 1));
            }
        }

        foreach (var member in root.DescendantNodes().OfType<MemberAccessExpressionSyntax>())
        {
            if (member.Name.Identifier.ValueText == "BaseDirectory"
                && RightmostName(member.Expression) == "AppContext")
            {
                findings.Add(Finding(path, "System.AppContext.BaseDirectory", member.GetLocation().GetLineSpan().StartLinePosition.Line + 1));
            }
        }

        return findings;
    }

    private static bool TryForbiddenStaticApi(MemberAccessExpressionSyntax member, out string api)
    {
        var expression = member.Expression.ToString();
        var owner = RightmostName(member.Expression);
        if (expression is "File" or "Directory" or "System.IO.File" or "System.IO.Directory")
        {
            api = $"System.IO.{owner}.{member.Name.Identifier.ValueText}";
            return true;
        }

        api = string.Empty;
        return false;
    }

    private static RepositoryIoAccessFinding Finding(string path, string api, int line) => new(
        path,
        api,
        $"line {line}: direct repository I/O is forbidden; use {ScribeTestsProject}.RepositoryAccessor");

    private static string RightmostName(SyntaxNode node) => node switch
    {
        IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
        QualifiedNameSyntax qualified => qualified.Right.Identifier.ValueText,
        AliasQualifiedNameSyntax alias => alias.Name.Identifier.ValueText,
        MemberAccessExpressionSyntax member => member.Name.Identifier.ValueText,
        _ => string.Empty,
    };
}
