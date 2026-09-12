using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AnchorReferenceRuleTests
{
    private const string Target = "Mathlib.Data.Nat.Fib.Zeckendorf";

    [Fact]
    public void Sl017AddedModuleWithUnreachableAnchorIsReported()
    {
        var completed = ExecuteDelta(RuleFixture.RingPath, added: true);

        AssertAnchorFinding(completed);
    }

    [Fact]
    public void Sl017AddedModuleWithDirectAnchorImportPasses()
    {
        var completed = ExecuteDelta(RuleFixture.RingPath, added: true, directImport: true);

        Assert.Empty(AnchorDiagnostics(completed));
    }

    [Fact]
    public void Sl017UnrelatedLeanDeltaPreservesUntouchedFrozenAnchor()
    {
        var completed = ExecuteDelta("D5/S0/Carrier/Unrelated.lean");

        Assert.Empty(AnchorDiagnostics(completed));
    }

    [Fact]
    public void Sl017DependencyDeltaReportsUntouchedFrozenAnchor()
    {
        var completed = ExecuteDelta("D5/S0/Carrier/Helper.lean");

        AssertAnchorFinding(completed);
    }

    [Fact]
    public void Sl017LeanReportProducerDeltaReportsUntouchedFrozenAnchor()
    {
        var completed = ExecuteDelta("lean-toolchain");

        AssertAnchorFinding(completed);
    }

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

    private static IEnumerable<Diagnostic> AnchorDiagnostics(CompletedRuleSet completed) =>
        completed.Diagnostics.Where(static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(17));

    private static void AssertAnchorFinding(CompletedRuleSet completed)
    {
        var diagnostic = Assert.Single(AnchorDiagnostics(completed));
        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Equal(
            $"anchor 'mathlib/module/{Target}' is not reachable through this file's repository import closure",
            diagnostic.Message);
    }

    // Synthetic snapshots and policy: these applicability tests do not read repository data.
    private static CompletedRuleSet ExecuteDelta(
        string changedPath,
        bool added = false,
        bool directImport = false)
    {
        const string helper = "D5/S0/Carrier/Helper.lean";
        const string unrelated = "D5/S0/Carrier/Unrelated.lean";
        var ringImports = directImport ? new[] { Target } : new[] { "D5.S0.Carrier.Helper" };
        var report = Report(
            (RuleFixture.RingPath, ringImports),
            (helper, []),
            (unrelated, []));
        var current = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [RuleFixture.RingPath] = $"""
                /- GID: D5/S0/Carrier/Ring
                   generality: G
                   mirror-B: none(waiver:fixture)
                   mirror-E: none(waiver:fixture)
                   anchors: [mathlib/module/{Target}]
                   digest: Anchor scope fixture. -/
                import {ringImports[0]}
                """ + "\n",
            [helper] = "-- helper\n",
            [unrelated] = "-- unrelated\n",
            ["Library/queries.yaml"] = "schema_version: 1\nqueries: []\n",
            [RuleFixture.FixtureBackfillSourcePath] = RuleFixture.FixtureBackfillSource,
            [RuleFixture.FixtureDigestionSourcePath] = RuleFixture.FixtureDigestionSource,
            ["lean-toolchain"] = "leanprover/lean4:v4.23.0\n",
        };
        if (!added)
        {
            var path = RepoPath.CreateKnown(RuleFixture.RingPath);
            var statement = FrozenContentAddress.ComputeModuleStatementId(path, report.Files[path]);
            current[FrozenStatePath.FromModulePath(path).Value] =
                $"{{\"statement_id\":\"{statement.Value}\"}}\n";
        }

        var baseline = new Dictionary<string, string>(current, StringComparer.Ordinal);
        if (added)
        {
            baseline.Remove(RuleFixture.RingPath);
        }
        else
        {
            current[changedPath] += "-- changed\n";
        }

        var policy = RegistryLoadAssert.Accepted(RegistryPolicyCompiler.Compile(
            new RegistrySyntax(1, [], [], [],
                [new ArtifactKindSyntax("lean", "lean-module", ["module"], ["formal"])]),
            [new DomainSyntax("Carrier", "S0", "Synthetic carrier")])).Policy;
        var changes = RawChangeSet.CreateWithKinds(
            [(changedPath, added ? RawChangeKind.Added : RawChangeKind.Modified)]);
        var context = RuleEvaluationContext.Create(
            SyntheticSnapshot(current),
            SyntheticSnapshot(baseline),
            policy,
            AcceptedLeanClosure.Create(report),
            changes,
            MetaClear.Create());
        Assert.False(context.RuleImplementationChanged);
        var outcome = RuleCatalog.Default.Execute(context);
        Assert.True(outcome is RuleExecutionOutcome.Completed,
            outcome is RuleExecutionOutcome.InfrastructureFailure failure ? failure.Message : "execution failed");
        return Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;
    }

    private static RepositorySnapshot SyntheticSnapshot(IReadOnlyDictionary<string, string> files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(static file =>
                RawRepositoryEntry.FromText(file.Key, file.Value))))).Snapshot;

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
