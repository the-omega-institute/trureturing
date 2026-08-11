using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal static class RepositoryRootCriterionMappingPolicy
{
    private const string ProjectPrefix = "Meta/StrataLint/StrataLint.Scribe.Tests/";

    internal static IReadOnlyList<RepositoryIoAccessFinding> InspectRepository(
        string repositoryRoot,
        IReadOnlyDictionary<string, string> historicalCriteria)
    {
        var findings = new List<RepositoryIoAccessFinding>();
        var observedPaths = new HashSet<string>(StringComparer.Ordinal);
        foreach (var file in GitIndexRepositoryFiles.Enumerate(repositoryRoot).Where(static file =>
                     file.RelativePath.StartsWith(ProjectPrefix, StringComparison.Ordinal)
                     && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)))
        {
            var projectPath = file.RelativePath[ProjectPrefix.Length..];
            var source = File.ReadAllText(file.FullPath);
            var sourceFindings = InspectSource(
                projectPath,
                source,
                historicalCriteria);
            if (ContainsDiscoverCall(source))
            {
                observedPaths.Add(projectPath);
            }

            findings.AddRange(sourceFindings);
        }

        findings.AddRange(historicalCriteria.Keys.Except(observedPaths, StringComparer.Ordinal).Select(path =>
            new RepositoryIoAccessFinding(path, "MISSING", "historical repository-root call site is absent")));
        return findings;
    }

    internal static IReadOnlyList<RepositoryIoAccessFinding> InspectSource(
        string path,
        string source,
        IReadOnlyDictionary<string, string> historicalCriteria)
    {
        var actual = DiscoverCalls(source).Select(static call => call.Criterion).ToArray();
        var expected = historicalCriteria.GetValueOrDefault(path)?.Split(',') ?? [];
        if (actual.SequenceEqual(expected, StringComparer.Ordinal))
        {
            return [];
        }

        return
        [
            new RepositoryIoAccessFinding(
                path,
                string.Join(',', actual),
                $"repository root criteria must be the historical sequence {string.Join(',', expected)}"),
        ];
    }

    private static bool ContainsDiscoverCall(string source) => DiscoverCalls(source).Count > 0;

    private static IReadOnlyList<(string Criterion, int Line)> DiscoverCalls(string source)
    {
        var root = CSharpSyntaxTree.ParseText(source).GetRoot();
        return root.DescendantNodes().OfType<InvocationExpressionSyntax>()
            .Where(static invocation => invocation.Expression is MemberAccessExpressionSyntax
                {
                    Expression: IdentifierNameSyntax { Identifier.ValueText: "RepositoryAccessor" },
                    Name.Identifier.ValueText: "Discover",
                })
            .Select(static invocation =>
            {
                var argument = invocation.ArgumentList.Arguments.LastOrDefault()?.Expression;
                var criterion = argument is MemberAccessExpressionSyntax member
                    && member.Expression is IdentifierNameSyntax { Identifier.ValueText: "RepositoryRootCriterion" }
                        ? member.Name.Identifier.ValueText
                        : "UNRECOGNIZED";
                return (criterion, invocation.GetLocation().GetLineSpan().StartLinePosition.Line + 1);
            })
            .ToArray();
    }
}
