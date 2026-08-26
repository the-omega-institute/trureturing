using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace StrataLint.ArchitectureTests;

public sealed class RetiredLedgerSurfaceTests
{
    [Fact]
    public void ProductionCodeContainsNoReattestProtocolIdentifiersOrLiterals()
    {
        var findings = InspectProductionCode(
            static token => token.ValueText.Contains("Reattest", StringComparison.Ordinal),
            static line => line.Contains("Reattest", StringComparison.Ordinal));

        Assert.Empty(findings);
    }

    [Fact]
    public void ProductionCodeContainsNoLedgerSyncLiteral()
    {
        var findings = InspectProductionCode(
            static token => token.ValueText.Contains("ledger-sync", StringComparison.Ordinal),
            static line => line.Contains("ledger-sync", StringComparison.Ordinal));

        Assert.Empty(findings);
    }

    private static IReadOnlyList<string> InspectProductionCode(
        Func<SyntaxToken, bool> csharpPredicate,
        Func<string, bool> textPredicate)
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var findings = new List<string>();
        foreach (var file in GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => IsProductionCodePath(file.RelativePath)))
        {
            if (file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            {
                var root = CSharpSyntaxTree.ParseText(
                    File.ReadAllText(file.FullPath),
                    CSharpParseOptions.Default.WithLanguageVersion(LanguageVersion.Preview),
                    file.RelativePath).GetRoot();
                findings.AddRange(root.DescendantTokens()
                    .Where(csharpPredicate)
                    .Select(token => $"{file.RelativePath}:{token.GetLocation().GetLineSpan().StartLinePosition.Line + 1}:{token.ValueText}"));
                continue;
            }

            findings.AddRange(File.ReadLines(file.FullPath)
                .Select(static (line, index) => (Line: line, Number: index + 1))
                .Where(static item => !item.Line.TrimStart().StartsWith('#'))
                .Where(item => textPredicate(item.Line))
                .Select(item => $"{file.RelativePath}:{item.Number}:{item.Line.Trim()}"));
        }

        return findings;
    }

    private static bool IsProductionCodePath(string path) =>
        !path.StartsWith("tools/tests/", StringComparison.Ordinal)
        && !path.StartsWith("D5/", StringComparison.Ordinal)
        && !path.StartsWith("docs/", StringComparison.Ordinal)
        && !path.StartsWith("Golden/", StringComparison.Ordinal)
        && (path.StartsWith("tools/", StringComparison.Ordinal)
            || path.StartsWith(".github/", StringComparison.Ordinal))
        && (path.EndsWith(".cs", StringComparison.Ordinal)
            || path.EndsWith(".sh", StringComparison.Ordinal)
            || path.EndsWith(".yml", StringComparison.Ordinal)
            || path.EndsWith(".yaml", StringComparison.Ordinal)
            || path.EndsWith("Makefile", StringComparison.Ordinal)
            || path.EndsWith(".mk", StringComparison.Ordinal));
}
