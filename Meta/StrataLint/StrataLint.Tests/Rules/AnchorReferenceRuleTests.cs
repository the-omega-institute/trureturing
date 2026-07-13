using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AnchorReferenceRuleTests
{
    private const string CatalogPath = "Meta/StrataLint/Generated/anchor-catalog.v1.json";
    private const string GictPath = "docs/develop/theory/GICT_complete_development_v3_3.md";

    [Fact]
    public void CanonicalRegisteredResolvedAnchorPasses()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.1/definition/1.1");

        var result = Evaluate(fixture);

        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void TheoryMarkdownIsNotReadByLint()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.2/definition/1.4");
        fixture.Files.Remove(GictPath);
        fixture.Baseline.Remove(GictPath);

        var result = Evaluate(fixture);

        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void ExistingCorpusUsesOnlyCanonicalAnchors()
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

        var queries = File.ReadAllText(
            Path.Combine(root, "Library", "queries.yaml"),
            Encoding.UTF8);
        fixture.Files["Library/queries.yaml"] = queries;
        fixture.Baseline["Library/queries.yaml"] = queries;

        var result = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(17),
            fixture.BuildForRuleCompatibility());

        Assert.DoesNotContain(result.Diagnostics, static diagnostic =>
            diagnostic.AdmissionEffect == AdmissionEffect.Block);
        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void CanonicalUnregisteredAnchorBlocks()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.1/theorem/9.9");

        var diagnostic = Assert.Single(Evaluate(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("unregistered", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ExternalCatalogMemberNeedsNoRuntimeReceipt()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(
            fixture,
            "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf");
        fixture.Files.Remove("lake-manifest.json");
        fixture.Baseline.Remove("lake-manifest.json");
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"]
            .Replace(
                "  - case_id: D5-T0016\n    gid: D5/X_Frontier/GovernanceDeferrals\n",
                string.Empty,
                StringComparison.Ordinal);

        var result = Evaluate(fixture);

        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void UnregisteredAnchorBlocksEvenWhenBaselineMatches()
    {
        var fixture = new RuleFixture();
        SetBaselineAndCurrentAnchors(fixture, "GICT-v3.6-I.2-theorem-2.9");

        var diagnostic = Assert.Single(Evaluate(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("unregistered", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void TheoryMarkdownDriftDoesNotAffectMembership()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.1/definition/1.1");
        fixture.Files[GictPath] = "# unrelated reference draft\nsource drift\n";

        var result = Evaluate(fixture);

        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void TheoryBackfillBindingDoesNotAffectMembership()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.1/definition/1.1");
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"]
            .Replace(GictPath, "docs/develop/theory/wrong.md", StringComparison.Ordinal);

        var result = Evaluate(fixture);

        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void TheoryHeadingContextDoesNotAffectMembership()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.1/definition/1.1");
        fixture.Files[GictPath] = "## I.2 \n**definition 1.1** duplicate target\n";
        var result = Evaluate(fixture);

        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void MissingCatalogFailsClosedAsInfrastructure()
    {
        var fixture = new RuleFixture();
        fixture.Files.Remove(CatalogPath);

        var outcome = RuleCatalog.Default.Execute(fixture.Build());

        var failure = Assert.IsType<RuleExecutionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("anchor catalog", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void NoncanonicalCatalogBytesFailClosedAsInfrastructure()
    {
        var fixture = new RuleFixture();
        fixture.Files[CatalogPath] += " ";

        var outcome = RuleCatalog.Default.Execute(fixture.Build());

        var failure = Assert.IsType<RuleExecutionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("canonical", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    private static SingleRuleEvaluation Evaluate(RuleFixture fixture) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(17), fixture.Build());

    private static void SetCurrentAnchors(RuleFixture fixture, params string[] anchors)
    {
        fixture.Files[RuleFixture.RingPath] = ReplaceAnchors(
            fixture.Files[RuleFixture.RingPath],
            anchors);
        fixture.Changes.Add(RuleFixture.RingPath);
    }

    private static void SetBaselineAndCurrentAnchors(
        RuleFixture fixture,
        params string[] anchors)
    {
        SetCurrentAnchors(fixture, anchors);
        fixture.Baseline[RuleFixture.RingPath] = ReplaceAnchors(
            fixture.Baseline[RuleFixture.RingPath],
            anchors);
    }

    private static string ReplaceAnchors(string text, IEnumerable<string> anchors) =>
        text.Replace(
            "anchors: []",
            "anchors: [" + string.Join(", ", anchors) + "]",
            StringComparison.Ordinal);

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "Meta", "BACKFILL.yaml")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
