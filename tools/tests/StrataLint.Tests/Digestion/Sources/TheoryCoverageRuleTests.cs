using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// The check that makes an undigested volume impossible to miss. A digestion source has
/// always had to name a governed document; nothing asked the question the other way round,
/// so a governed theory document with no source produced no symptom at all — the reader
/// that would have noticed was the one that was missing.
///
/// The volumes come from the TREE, never from a list injected here. Theory volumes are
/// governed by the path rule (a third-party volume name cannot be pre-enumerated), so
/// feeding the check a hand-built governance_documents list would pin it against a registry
/// state the repository does not have — the production path could go vacuous while these
/// tests stayed green. That is exactly what happened once.
/// </summary>
public sealed class TheoryCoverageRuleTests
{
    private const string GovernedPath = "docs/develop/theory/GOVERNED.md";
    private const string DigestedPath = "docs/develop/theory/DIGESTED.md";

    private static string[] Findings(params string[] treeTheoryDocuments)
    {
        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));
        var policy = RegistryLoadAssert.Accepted(outcome).Policy;
        var snapshot = DigestionTestSupport.Snapshot(
            treeTheoryDocuments
                .Select(static path => (path, Encoding.UTF8.GetBytes("# 卷\n")))
                .ToArray());
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
    public void ATheoryDocumentInTheTreeWithNoDigestionSourceIsReported()
    {
        var findings = Findings(GovernedPath, DigestedPath);

        var finding = Assert.Single(findings, message =>
            message.Contains("has no digestion source", StringComparison.Ordinal));
        Assert.Contains(GovernedPath, finding, StringComparison.Ordinal);
        Assert.Contains("make ingest", finding, StringComparison.Ordinal);
    }

    [Fact]
    public void ATheoryDocumentThatHasASourceIsNotReported()
    {
        var findings = Findings(DigestedPath);

        Assert.DoesNotContain(
            findings,
            static message => message.Contains("has no digestion source", StringComparison.Ordinal));
    }

    [Fact]
    public void AVolumeAbsentFromRegistryGovernanceIsStillReported()
    {
        // The registry used here is the real one, which enumerates no theory volume at all.
        // Before the path rule this case produced no finding: the loop had nothing to iterate.
        Assert.DoesNotContain("docs/develop/theory/", TestRegistry.Canonical, StringComparison.Ordinal);

        var findings = Findings(GovernedPath, DigestedPath);

        Assert.Contains(
            findings,
            static message => message.Contains("has no digestion source", StringComparison.Ordinal));
    }
}
