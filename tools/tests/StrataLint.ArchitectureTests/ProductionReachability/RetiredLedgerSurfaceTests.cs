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

    [Fact]
    public void ProductionCodeContainsNoHistoricalDagSchemaCompatibility()
    {
        var findings = InspectProductionCode(
            static token => token.ValueText is "FreezePayloadFieldsV3"
                || token.ValueText.Contains("must be 2, 3, or 4", StringComparison.Ordinal),
            static line => line.Contains("2 or 3 or CurrentDagSchemaVersion", StringComparison.Ordinal));

        Assert.Empty(findings);
    }

    [Fact]
    public void ProductionCodeContainsNoV1LedgerEnvelopeCompatibility()
    {
        var findings = InspectProductionCode(
            static token => token.ValueText is "EnvelopeField" or "V1EnvelopeFields",
            static line => line.Contains("V1EnvelopeFields", StringComparison.Ordinal)).ToList();
        findings.AddRange(InspectSourceFile(
            "tools/StrataLint.Engine/Ledger/FrozenLedgerReferenceScan.cs",
            static token => token.ValueText is "previous_hash" or "sequence"));

        Assert.Empty(findings);
    }

    [Fact]
    public void ProductionCodeContainsNoLedgerSupersedeProtocol()
    {
        var findings = InspectProductionCode(
            static token => token.ValueText.Contains("Supersede", StringComparison.Ordinal),
            static line => line.Contains("ledger-supersede", StringComparison.Ordinal),
            IsFrozenLedgerProtocolPath);

        Assert.Empty(findings);
    }

    [Fact]
    public void ProductionCodeContainsNoFrozenInputMaterializer()
    {
        var findings = InspectProductionCode(
            static token => token.ValueText.Contains("Materializer", StringComparison.Ordinal)
                || token.ValueText.Contains("materializer", StringComparison.Ordinal),
            static line => line.Contains("repository-snapshot-v1", StringComparison.Ordinal),
            IsFrozenLedgerProtocolPath);

        Assert.Empty(findings);
    }

    private static IReadOnlyList<string> InspectProductionCode(
        Func<SyntaxToken, bool> csharpPredicate,
        Func<string, bool> textPredicate,
        Func<string, bool>? pathPredicate = null)
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var findings = new List<string>();
        foreach (var file in GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(file => IsProductionCodePath(file.RelativePath)
                && (pathPredicate is null || pathPredicate(file.RelativePath))))
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

    private static IReadOnlyList<string> InspectSourceFile(
        string relativePath,
        Func<SyntaxToken, bool> predicate)
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var fullPath = Path.Combine(repositoryRoot, relativePath);
        var root = CSharpSyntaxTree.ParseText(
            File.ReadAllText(fullPath),
            CSharpParseOptions.Default.WithLanguageVersion(LanguageVersion.Preview),
            relativePath).GetRoot();
        return root.DescendantTokens()
            .Where(predicate)
            .Select(token => $"{relativePath}:{token.GetLocation().GetLineSpan().StartLinePosition.Line + 1}:{token.ValueText}")
            .ToArray();
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

    private static bool IsFrozenLedgerProtocolPath(string path) =>
        path.Contains("FrozenLedger", StringComparison.Ordinal)
        || path.Contains("/Commands/Ledger/", StringComparison.Ordinal)
        || path.EndsWith("CliApplication.cs", StringComparison.Ordinal)
        || path.EndsWith("ProductionCliEnvironment.cs", StringComparison.Ordinal)
        || path.EndsWith("RevocationPlanner.cs", StringComparison.Ordinal)
        || path.EndsWith("playbook-workflows.sh", StringComparison.Ordinal);
}
