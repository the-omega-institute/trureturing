using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AnchorReferenceRuleTests
{
    private const string Target = "Mathlib.Data.Nat.Fib.Zeckendorf";

    [Fact]
    public void ImportClosureAcceptsDirectImport() =>
        Assert.True(IsReachable(("D5/A.lean", [Target])));

    [Fact]
    public void ImportClosureAcceptsTwoHopImport() =>
        Assert.True(IsReachable(
            ("D5/A.lean", ["D5.B"]),
            ("D5/B.lean", [Target])));

    [Fact]
    public void ImportClosureAcceptsThreeHopImport() =>
        Assert.True(IsReachable(
            ("D5/A.lean", ["D5.B"]),
            ("D5/B.lean", ["D5.C"]),
            ("D5/C.lean", [Target])));

    [Fact]
    public void ImportClosureRejectsUnreachableTarget() =>
        Assert.False(IsReachable(("D5/A.lean", ["Mathlib.Data.Nat.Fib.Basic"])));

    [Fact]
    public void ImportClosureTerminatesOnCycle() =>
        Assert.False(IsReachable(
            ("D5/A.lean", ["D5.B"]),
            ("D5/B.lean", ["D5.A"])));

    [Fact]
    public void ImportClosureRejectsMissingStartModule() =>
        Assert.False(LeanImportClosure.ImportsExternalModule(
            Report(("D5/B.lean", [Target])),
            "D5.Missing",
            Target));

    [Fact]
    public void DeclaredDirectMathlibImportPasses()
    {
        var fixture = FixtureWithAnchor("mathlib/module/" + Target);
        fixture.Reports[RuleFixture.RingPath] = LeanReport([Target]);

        Assert.Empty(EvaluateMembership(fixture).Diagnostics);
    }

    [Fact]
    public void DeclaredTransitiveMathlibImportPasses()
    {
        var fixture = FixtureWithAnchor("mathlib/module/" + Target);
        fixture.Reports[RuleFixture.RingPath] = LeanReport(["D5.S0.Carrier.Helper"]);
        fixture.Files["D5/S0/Carrier/Helper.lean"] = "def helper : Nat := 0\n";
        fixture.Reports["D5/S0/Carrier/Helper.lean"] = LeanReport([Target]);

        Assert.Empty(EvaluateMembership(fixture).Diagnostics);
    }

    [Fact]
    public void DeclaredUnreachableMathlibImportBlocksWithPathAndCriterion()
    {
        var fixture = FixtureWithAnchor("mathlib/module/" + Target);

        var diagnostic = Assert.Single(EvaluateMembership(fixture).Diagnostics);

        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains("mathlib/module/" + Target, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("repository import closure", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DeclaredDirectLakeModuleImportPasses()
    {
        var fixture = FixtureWithAnchor("lake/module/" + Target);
        fixture.Reports[RuleFixture.RingPath] = LeanReport([Target]);

        Assert.Empty(EvaluateMembership(fixture).Diagnostics);
    }

    [Fact]
    public void DeclaredTransitiveLakeModuleImportPasses()
    {
        var fixture = FixtureWithAnchor("lake/module/" + Target);
        fixture.Reports[RuleFixture.RingPath] = LeanReport(["D5.S0.Carrier.Helper"]);
        fixture.Files["D5/S0/Carrier/Helper.lean"] = "def helper : Nat := 0\n";
        fixture.Reports["D5/S0/Carrier/Helper.lean"] = LeanReport([Target]);

        Assert.Empty(EvaluateMembership(fixture).Diagnostics);
    }

    [Fact]
    public void DeclaredUnreachableLakeModuleImportBlocksWithPathAndCriterion()
    {
        var fixture = FixtureWithAnchor("lake/module/" + Target);

        var diagnostic = Assert.Single(EvaluateMembership(fixture).Diagnostics);

        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains("lake/module/" + Target, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("repository import closure", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EmptyAnchorsPass()
    {
        var fixture = new RuleFixture();

        Assert.Empty(EvaluateMembership(fixture).Diagnostics);
    }

    // The retired registry held exactly one anchor, so it rejected every literature and declaration
    // anchor as unregistered. The import graph cannot decide those shapes either, so they stay
    // rejected — replacing the authority must not quietly widen what a header may claim.
    [Fact]
    public void LiteratureAnchorIsRejectedAsUndecidable()
    {
        var fixture = FixtureWithAnchor("lit/sos1957threegap");

        var diagnostic = Assert.Single(EvaluateMembership(fixture).Diagnostics);

        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains("lit/sos1957threegap", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("cannot be decided", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MathlibDeclarationAnchorIsRejectedAsUndecidable()
    {
        var fixture = FixtureWithAnchor("mathlib/decl/Nat.zeckendorf");
        fixture.Reports[RuleFixture.RingPath] = LeanReport([Target]);

        var diagnostic = Assert.Single(EvaluateMembership(fixture).Diagnostics);

        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains("mathlib/decl/Nat.zeckendorf", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("cannot be decided", diagnostic.Message, StringComparison.Ordinal);
    }

    private static bool IsReachable(params (string Path, string[] Imports)[] files) =>
        LeanImportClosure.ImportsExternalModule(Report(files), "D5.A", Target);

    private static LeanAxiomReport Report(params (string Path, string[] Imports)[] files) =>
        LeanAxiomReport.Create(files.ToDictionary(
            static file => file.Path,
            static file => LeanReport(file.Imports),
            StringComparer.Ordinal));

    private static LeanFileReport LeanReport(IEnumerable<string> imports) =>
        new(imports.ToImmutableArray(), ImmutableArray<LeanDeclaration>.Empty);

    private static RuleFixture FixtureWithAnchor(string anchor)
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath].Replace(
            "anchors: []",
            $"anchors: [{anchor}]",
            StringComparison.Ordinal);
        fixture.Changes.Add(RuleFixture.RingPath);
        return fixture;
    }

    private static SingleRuleEvaluation EvaluateMembership(RuleFixture fixture) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(17), fixture.Build());

}
