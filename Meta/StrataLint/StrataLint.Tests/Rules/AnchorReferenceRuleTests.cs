using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AnchorReferenceRuleTests
{
    private const string CatalogPath = "Meta/StrataLint/Generated/anchor-catalog.v1.json";

    [Fact]
    public void CanonicalRegisteredMathlibAnchorPasses()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf");

        var result = EvaluateMembership(fixture);

        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void CanonicalUnregisteredLiteratureAnchorBlocks()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "lit/sos1957threegap");

        var diagnostic = Assert.Single(EvaluateMembership(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("unregistered", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MalformedExternalAnchorBlocksUnderFormatRule()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "mathlib/symbol/Nat.zeckendorf");

        var diagnostic = Assert.Single(EvaluateFormat(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("canonical external anchor", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RuleDecisionUsesTypedCatalogInsteadOfCommittedProjection()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf");
        fixture.Files[CatalogPath] = fixture.Files[CatalogPath].Replace(
            "Mathlib.Data.Nat.Fib.Zeckendorf",
            "Mathlib.Data.Nat.Fib.Basic",
            StringComparison.Ordinal);

        Assert.Empty(EvaluateFormat(fixture).Diagnostics);
        Assert.Empty(EvaluateMembership(fixture).Diagnostics);

        fixture.Files.Remove(CatalogPath);

        Assert.Empty(EvaluateFormat(fixture).Diagnostics);
        Assert.Empty(EvaluateMembership(fixture).Diagnostics);
    }

    [Fact]
    public void UncatalogedOpaqueAnchorBlocksUnderFormatRule()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "legacy/v1/missing");

        var diagnostic = Assert.Single(EvaluateFormat(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("canonical external anchor", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ExistingCorpusUsesOnlyCanonicalRegisteredExternalAnchors()
    {
        var fixture = new RuleFixture();
        var root = FindRepositoryRoot();
        foreach (var path in Directory.EnumerateFiles(
            Path.Combine(root, "D5"),
            "*.lean",
            SearchOption.AllDirectories))
        {
            var relative = Path.GetRelativePath(root, path)
                .Replace(Path.DirectorySeparatorChar, '/');
            var text = File.ReadAllText(path, Encoding.UTF8);
            var report = new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray<LeanDeclaration>.Empty);
            fixture.Files[relative] = text;
            fixture.Baseline[relative] = text;
            fixture.Reports[relative] = report;
            fixture.BaselineReports[relative] = report;
        }

        var format = EvaluateFormat(fixture);
        var membership = EvaluateMembership(fixture);

        Assert.Empty(format.Diagnostics);
        Assert.Empty(membership.Diagnostics);
    }

    [Fact]
    public void ExternalCatalogMemberNeedsNoRuntimeReceipt()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf");
        fixture.Files.Remove("lake-manifest.json");
        fixture.Baseline.Remove("lake-manifest.json");

        var result = EvaluateMembership(fixture);

        Assert.Empty(result.Diagnostics);
    }

    private static SingleRuleEvaluation EvaluateFormat(RuleFixture fixture) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(15), fixture.Build());

    private static SingleRuleEvaluation EvaluateMembership(RuleFixture fixture) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(17), fixture.Build());

    private static void SetCurrentAnchors(RuleFixture fixture, params string[] anchors)
    {
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath].Replace(
            "anchors: []",
            "anchors: [" + string.Join(", ", anchors) + "]",
            StringComparison.Ordinal);
        fixture.Changes.Add(RuleFixture.RingPath);
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "global.json"))
                && Directory.Exists(Path.Combine(current.FullName, "Blueprint")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
