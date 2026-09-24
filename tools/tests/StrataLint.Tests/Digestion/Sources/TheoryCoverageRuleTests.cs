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

    /// <summary>
    /// FILEMAP registers the theory family without listing individual volumes. The check
    /// must enumerate the snapshot to report a volume with no digestion source.
    /// </summary>
    private static string[] Findings()
    {
        var outcome = RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(TestFileMap.Canonical),
            Encoding.UTF8.GetBytes(TestFileMap.Domains));
        var policy = PolicyLoadAssert.Accepted(outcome).Policy;
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
                DigestionTestSupport.Document(
                    AtomizerRegistry.GenericId,
                    [],
                    "digested",
                    DigestedPath,
                    GenreRegistryCheck.Collected([])))
            .Select(static finding => finding.Message)
            .ToArray();
    }

    [Fact]
    public void AGovernedTheoryDocumentWithNoDigestionSourceIsReported()
    {
        var findings = Findings();

        var finding = Assert.Single(findings, message =>
            message.Contains("has no digestion source", StringComparison.Ordinal));
        Assert.Contains(GovernedPath, finding, StringComparison.Ordinal);
        Assert.Contains("make ingest", finding, StringComparison.Ordinal);
    }

    // The undigested neighbor must still be reported; this assertion names the digested file.
    [Fact]
    public void ATheoryDocumentThatHasASourceIsNotReported()
    {
        var findings = Findings();

        Assert.DoesNotContain(
            findings,
            static message => message.Contains(DigestedPath, StringComparison.Ordinal)
                && message.Contains("has no digestion source", StringComparison.Ordinal));
    }
}
