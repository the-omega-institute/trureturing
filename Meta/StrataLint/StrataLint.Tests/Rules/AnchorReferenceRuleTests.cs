using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AnchorReferenceRuleTests
{
    private const string CatalogPath = "Meta/StrataLint/Generated/anchor-catalog.v1.json";
    private const string GictPath = "docs/develop/theory/GICT_complete_development_v3 (3).md";
    private const string GictHash = "d61cda25af5f6bf17b065711ee762b63d6d196f94dd77e5ece962cf146bc163c";

    [Fact]
    public void CanonicalRegisteredResolvedAnchorPasses()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.1/definition/1.1");

        var result = Evaluate(fixture);

        Assert.Empty(result.Diagnostics);
    }

    [Fact]
    public void GictSelectorIgnoresMatchingLabelOutsideItsRegisteredDivision()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.2/definition/1.4");
        fixture.Files[GictPath] = fixture.Files[GictPath].Replace(
            "## I.2 ",
            "**定义 1.4(三轴)**。wrong division\n\n## I.2 ",
            StringComparison.Ordinal);
        var replacementHash = Convert.ToHexStringLower(SHA256.HashData(
            Encoding.UTF8.GetBytes(fixture.Files[GictPath])));
        fixture.Files[CatalogPath] = fixture.Files[CatalogPath]
            .Replace(GictHash, replacementHash, StringComparison.Ordinal);

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
        Assert.Equal(4, result.Diagnostics.Count(static diagnostic =>
            diagnostic.AdmissionEffect == AdmissionEffect.Observe));
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
    public void RegisteredOpenAnchorObservesWithPermanentCase()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(
            fixture,
            "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf");

        var diagnostic = Assert.Single(Evaluate(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.Contains("D5-T0016", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("registered open", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RegisteredOpenWithoutBackfillCaseBlocks()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(
            fixture,
            "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf");
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"]
            .Replace(
                "  - case_id: D5-T0016\n    gid: D5/X_Frontier/GovernanceDeferrals\n",
                string.Empty,
                StringComparison.Ordinal);

        var diagnostic = Assert.Single(Evaluate(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("case D5-T0016", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("{\"packages\":[{\"name\":\"mathlib\",\"rev\":17}]}\n")]
    [InlineData("[]\n")]
    [InlineData("{\"packages\":[17]}\n")]
    public void MalformedMathlibPinBlocksAsInvalidTarget(string manifest)
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(
            fixture,
            "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf");
        fixture.Files["lake-manifest.json"] = manifest;

        var diagnostic = Assert.Single(Evaluate(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("invalid target", diagnostic.Message, StringComparison.Ordinal);
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
    public void FrozenSourceHashDriftBlocksAsInvalidTarget()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.1/definition/1.1");
        fixture.Files[GictPath] += "\nsource drift\n";

        var diagnostic = Assert.Single(Evaluate(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("invalid target", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("SHA-256", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BackfillTheorySourceBindingDriftBlocksAsInvalidTarget()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.1/definition/1.1");
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"]
            .Replace(GictPath, "docs/develop/theory/wrong.md", StringComparison.Ordinal);

        var diagnostic = Assert.Single(Evaluate(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("BACKFILL", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MultipleStructuralTargetsBlockAsAmbiguous()
    {
        var fixture = new RuleFixture();
        SetCurrentAnchors(fixture, "gict/v3.6/I.1/definition/1.1");
        fixture.Files[GictPath] = fixture.Files[GictPath].Replace(
            "## I.2 ",
            "**定义 1.1**。duplicate target\n\n## I.2 ",
            StringComparison.Ordinal);
        var replacementHash = Convert.ToHexStringLower(SHA256.HashData(
            Encoding.UTF8.GetBytes(fixture.Files[GictPath])));
        fixture.Files[CatalogPath] = fixture.Files[CatalogPath]
            .Replace(GictHash, replacementHash, StringComparison.Ordinal);

        var diagnostic = Assert.Single(Evaluate(fixture).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("ambiguous", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnreferencedInvalidCatalogDefinitionBlocks()
    {
        var fixture = new RuleFixture();
        AppendCatalogDefinition(fixture, new
        {
            anchor = "spec/v7.11/unused",
            case_id = (string?)null,
            expected_sha256 = new string('0', 64),
            open_reason = (string?)null,
            source_id = "golden-ledger-spec-v7.11",
            source_path = "docs/develop/spec/missing.md",
            source_revision = "v7.11",
            status = "resolved",
            structural_selector = "line-prefix:**missing**",
            target_key = "spec:v7.11:unused",
            target_kind = "spec-clause",
        });

        var diagnostic = Assert.Single(RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(17),
            fixture.BuildForProtectedRuleCompatibility()).Diagnostics);

        Assert.Equal(CatalogPath, diagnostic.Path);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("invalid target", diagnostic.Message, StringComparison.Ordinal);
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

    private static void AppendCatalogDefinition(RuleFixture fixture, object definition)
    {
        using var document = JsonDocument.Parse(fixture.Files[CatalogPath]);
        var definitions = document.RootElement.GetProperty("definitions")
            .EnumerateArray()
            .Select(static item => item.Clone())
            .Append(JsonSerializer.SerializeToElement(definition))
            .ToArray();
        var catalog = JsonSerializer.SerializeToElement(new
        {
            definitions,
            schema_version = 1,
        });
        fixture.Files[CatalogPath] = Encoding.UTF8.GetString(
            StructuredCanonicalWriter.WriteJson(catalog).AsSpan());
        fixture.Changes.Add(CatalogPath);
    }

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
