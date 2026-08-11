using System.Xml.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal sealed record TestSelectionSafetyFinding(string Path, int Line, string Message);

internal static class TestSelectionSafetyPolicy
{
    internal static IReadOnlySet<string> ProjectReferenceClosure(string projectPath)
    {
        var pending = new Stack<string>();
        var visited = new HashSet<string>(StringComparer.Ordinal);
        pending.Push(Path.GetFullPath(projectPath));
        while (pending.TryPop(out var current))
        {
            if (!visited.Add(current)) continue;
            var directory = Path.GetDirectoryName(current)
                ?? throw new InvalidOperationException($"project has no directory: {current}");
            var document = XDocument.Load(current, LoadOptions.SetLineInfo);
            foreach (var reference in document.Descendants("ProjectReference"))
            {
                var include = reference.Attribute("Include")?.Value;
                if (string.IsNullOrWhiteSpace(include))
                {
                    throw new InvalidDataException($"ProjectReference lacks Include: {current}");
                }

                var referenced = Path.GetFullPath(Path.Combine(directory, include));
                if (!File.Exists(referenced))
                {
                    throw new FileNotFoundException("referenced project does not exist", referenced);
                }

                pending.Push(referenced);
            }
        }

        return visited;
    }

    internal static IReadOnlyList<TestSelectionSafetyFinding> InspectProjectSources(
        string repositoryRoot,
        string projectDirectory,
        string pathPrefix)
    {
        var sources = CSharpRepositorySources.Enumerate(repositoryRoot).ToArray();
        var constantNames = sources
            .SelectMany(source => ConstantsForPrefix(File.ReadAllText(source.FullPath), pathPrefix))
            .ToHashSet(StringComparer.Ordinal);
        var normalizedProject = projectDirectory.TrimEnd('/') + "/";
        return sources
            .Where(source => source.RelativePath.StartsWith(normalizedProject, StringComparison.Ordinal))
            .SelectMany(source => InspectSource(
                source.RelativePath,
                File.ReadAllText(source.FullPath),
                pathPrefix,
                constantNames))
            .ToArray();
    }

    internal static IReadOnlyList<TestSelectionSafetyFinding> InspectSource(
        string path,
        string source,
        string pathPrefix,
        IReadOnlySet<string> pathConstantNames)
    {
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        var uses = root.DescendantNodes()
            .Where(node => IsPathLiteral(node, pathPrefix) || IsConstantConsumer(node, pathConstantNames));
        return uses
            .Select(use => UnsafeFileSystemUse(use))
            .Where(static use => use is not null)
            .Select(use => new TestSelectionSafetyFinding(
                path,
                use!.GetLocation().GetLineSpan().StartLinePosition.Line + 1,
                "repository path can reach a non-temporary file-system read"))
            .ToArray();
    }

    private static IEnumerable<string> ConstantsForPrefix(string source, string pathPrefix)
    {
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        return root.DescendantNodes().OfType<VariableDeclaratorSyntax>()
            .Where(static variable => variable.Parent?.Parent is FieldDeclarationSyntax field
                && field.Modifiers.Any(static modifier => modifier.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.ConstKeyword)))
            .Where(variable => variable.Initializer?.Value is LiteralExpressionSyntax literal
                && literal.Token.ValueText.StartsWith(pathPrefix, StringComparison.Ordinal))
            .Select(static variable => variable.Identifier.ValueText);
    }

    private static bool IsPathLiteral(Microsoft.CodeAnalysis.SyntaxNode node, string pathPrefix) =>
        node is LiteralExpressionSyntax literal
        && literal.Token.ValueText.StartsWith(pathPrefix, StringComparison.Ordinal);

    private static bool IsConstantConsumer(
        Microsoft.CodeAnalysis.SyntaxNode node,
        IReadOnlySet<string> names) =>
        node is IdentifierNameSyntax identifier
        && names.Contains(identifier.Identifier.ValueText)
        && identifier.Parent is not VariableDeclaratorSyntax;

    private static InvocationExpressionSyntax? UnsafeFileSystemUse(Microsoft.CodeAnalysis.SyntaxNode use)
    {
        var invocation = use.Ancestors().OfType<InvocationExpressionSyntax>().FirstOrDefault();
        if (invocation is null) return null;
        var call = invocation.Expression.ToString();
        if (!IsFileSystemCall(call)) return null;

        if (call.EndsWith("Path.Combine", StringComparison.Ordinal)
            || call.Equals("Path.Combine", StringComparison.Ordinal))
        {
            var first = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression.ToString() ?? "";
            if (IsTemporaryRoot(invocation, first))
            {
                return null;
            }
        }

        return invocation;
    }

    private static bool IsFileSystemCall(string call) =>
        call.StartsWith("File.", StringComparison.Ordinal)
        || call.StartsWith("Directory.", StringComparison.Ordinal)
        || call.EndsWith("Path.Combine", StringComparison.Ordinal)
        || call.Equals("Path.Combine", StringComparison.Ordinal);

    private static bool ContainsRepositoryRoot(string expression) =>
        expression.Contains("AppContext.BaseDirectory", StringComparison.Ordinal)
        || expression.Contains("Environment.CurrentDirectory", StringComparison.Ordinal)
        || expression.Contains("Directory.GetCurrentDirectory", StringComparison.Ordinal)
        || expression.Contains("RepositoryLayout.FindRoot", StringComparison.Ordinal);

    private static bool IsTemporaryRoot(InvocationExpressionSyntax invocation, string first)
    {
        if (ContainsRepositoryRoot(first)) return false;
        if (first.Contains(".Path", StringComparison.Ordinal)) return true;
        var type = invocation.Ancestors().OfType<TypeDeclarationSyntax>().FirstOrDefault();
        return type is not null
            && type.DescendantNodes().OfType<VariableDeclarationSyntax>()
                .Any(static declaration => declaration.Type.ToString().EndsWith("TemporaryDirectory", StringComparison.Ordinal))
            && type.DescendantNodes().OfType<AssignmentExpressionSyntax>()
                .Any(assignment => assignment.Left.ToString() == first
                    && assignment.Right.ToString().EndsWith(".Path", StringComparison.Ordinal));
    }
}
