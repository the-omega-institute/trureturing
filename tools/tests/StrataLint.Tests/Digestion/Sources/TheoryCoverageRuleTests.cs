using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// The check that makes an undigested volume impossible to miss. A digestion source has
/// always had to name a governed document; nothing asked the question the other way round,
/// so a governed theory document with no source produced no symptom at all — the reader
/// that would have noticed was the one that was missing.
/// </summary>
public sealed class TheoryCoverageRuleTests
{
    private const string GovernedPath = "docs/develop/theory/GOVERNED.md";
    private const string DigestedPath = "docs/develop/theory/DIGESTED.md";

    /// <summary>The loader requires canonical bytes, so the paths go in sorted position.</summary>
    private static string Registry(params string[] theoryDocuments) =>
        TestRegistry.Canonical.Replace(
            "  - \"docs/develop/spec/golden-ledger-repo-spec.md\"\n",
            "  - \"docs/develop/spec/golden-ledger-repo-spec.md\"\n"
            + string.Concat(theoryDocuments
                .Order(StringComparer.Ordinal)
                .Select(static path => $"  - \"{path}\"\n")),
            StringComparison.Ordinal);

    private static string Ledger() => string.Join(
        "\n",
        "schema_version: 3",
        "ledger: theory-digestion-v1",
        "sources:",
        "  - source_id: digested",
        "    path: " + DigestedPath,
        "    atomizer: " + AtomizerRegistry.GenericId,
        "    entries: []");

    private static string[] Findings(string registry)
    {
        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(registry),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));
        var policy = RegistryLoadAssert.Accepted(outcome).Policy;
        var snapshot = DigestionTestSupport.Snapshot(
            (GovernedPath, Encoding.UTF8.GetBytes("# 未消化\n")),
            (DigestedPath, Encoding.UTF8.GetBytes("# 已消化\n")));
        return BackfillInventoryRule.EvaluateDocument(
                new BackfillInventoryValidationContext(
                    snapshot,
                    snapshot,
                    policy,
                    DigestionTestSupport.AcceptedLean(Array.Empty<string>()),
                    null),
                BackfillInventoryLoader.Load(Ledger()))
            .Select(static finding => finding.Message)
            .ToArray();
    }

    [Fact]
    public void AGovernedTheoryDocumentWithNoDigestionSourceIsReported()
    {
        var findings = Findings(Registry(GovernedPath, DigestedPath));

        var finding = Assert.Single(findings, message =>
            message.Contains("has no digestion source", StringComparison.Ordinal));
        Assert.Contains(GovernedPath, finding, StringComparison.Ordinal);
        Assert.Contains("make ingest", finding, StringComparison.Ordinal);
    }

    [Fact]
    public void ATheoryDocumentThatHasASourceIsNotReported()
    {
        var findings = Findings(Registry(DigestedPath));

        Assert.DoesNotContain(
            findings,
            static message => message.Contains("has no digestion source", StringComparison.Ordinal));
    }
}
