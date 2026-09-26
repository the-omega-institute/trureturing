using StrataLint.Configuration;
using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Rules.Tests;

public sealed class AnchorReferenceRuleTests
{
    private const string Target = "Mathlib.Data.Nat.Fib.Zeckendorf";
    private const string HelperPath = "D5/S0/Carrier/Helper.lean";
    private const string IntermediatePath = "D5/S0/Carrier/Intermediate.lean";
    private const string FurtherPath = "D5/S0/Carrier/Further.lean";
    private const string UnrelatedPath = "D5/S0/Carrier/Unrelated.lean";

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
    public void Sl017ReportsUnchangedImporterWhenDirectDependencyRemovesAnchorImport()
    {
        var (baseline, candidate) = PairedImportContexts(false, HelperPath);

        AssertPairedAnchorChecks(baseline, candidate, HelperPath, affected: true, reachableAfter: false);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Sl017ReportsUnchangedImporterWhenIntermediateDependencyRewritesFurtherImport(bool replace)
    {
        var (baseline, candidate) = PairedImportContexts(
            true, IntermediatePath, replace ? ["D5.S0.Carrier.Unrelated"] : []);
        var importer = RepoPath.CreateKnown(RuleFixture.RingPath);

        Assert.Contains(RepoPath.CreateKnown(FurtherPath),
            LeanImportClosure.RepositoryPaths(baseline.Lean.Report, importer));
        Assert.DoesNotContain(RepoPath.CreateKnown(FurtherPath),
            LeanImportClosure.RepositoryPaths(candidate.Lean.Report, importer));
        Assert.Equal(replace, LeanImportClosure.RepositoryPaths(candidate.Lean.Report, importer)
            .Contains(RepoPath.CreateKnown(UnrelatedPath)));
        AssertPairedAnchorChecks(baseline, candidate, IntermediatePath, affected: true, reachableAfter: false);
    }

    [Fact]
    public void Sl017PairedUnrelatedChangeLeavesReachableImporterUnselected()
    {
        var (baseline, candidate) = PairedImportContexts(true, UnrelatedPath);

        AssertPairedAnchorChecks(baseline, candidate, UnrelatedPath, affected: false, reachableAfter: true);
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

    [Theory]
    [InlineData("tools/lean-inspector", "LeanInformationAudit.Syntax")]
    [InlineData("tools/lean-inspector", "LeanInformationAuditAnalysis.Probe")]
    [InlineData("tools/lean-inspector-interface", "LeanInformationAuditInterface.Syntax")]
    public void ImportClosureUsesInspectorSourceRootForTooling(string sourceRoot, string module)
    {
        var path = sourceRoot + "/" + module.Replace('.', '/') + ".lean";
        var report = Report(("D5/A.lean", [module]), (path, ["D5.B"]),
            ("D5/B.lean", [Target]));
        Assert.Equal(module, LeanImportClosure.ModuleName(RepoPath.CreateKnown(path)));
        Assert.Contains(RepoPath.CreateKnown("D5/B.lean"),
            LeanImportClosure.RepositoryPaths(report, RepoPath.CreateKnown("D5/A.lean")));
        Assert.True(LeanImportClosure.ImportsExternalModule(report, "D5.A", Target));
    }

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

    private static Dictionary<string, string> SyntheticFiles(string[] ringImports) =>
        new(StringComparer.Ordinal)
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
            [HelperPath] = "-- helper\n",
            [UnrelatedPath] = "-- unrelated\n",
            ["Library/queries.yaml"] = "schema_version: 1\nqueries: []\n",
            [EngineeringRegistrationFixture.Path] = EngineeringRegistrationFixture.Manifest(),
            [RuleFixture.FixtureBackfillSourcePath] = RuleFixture.FixtureBackfillSource,
            [RuleFixture.FixtureDigestionSourcePath] = RuleFixture.FixtureDigestionSource,
            ["lean-toolchain"] = "leanprover/lean4:v4.23.0\n",
        };

    private static void PinImporter(Dictionary<string, string> files, LeanAxiomReport report)
    {
        var path = RepoPath.CreateKnown(RuleFixture.RingPath);
        var statement = FrozenContentAddress.ComputeModuleStatementId(path, report.Files[path]);
        files[FrozenStatePath.FromModulePath(path).Value] =
            $"{{\"statement_id\":\"{statement.Value}\"}}\n";
    }

    // Synthetic rule-level evidence only: source imports and report imports share fixture data.
    // These tests do not establish actual compiler/report correspondence.
    private static (DeltaRuleContext Baseline, DeltaRuleContext Candidate) PairedImportContexts(
        bool throughIntermediate,
        string changedPath,
        params string[] candidateImports)
    {
        (string Path, string[] Imports)[] modules =
        [
            (RuleFixture.RingPath, ["D5.S0.Carrier.Helper"]),
            (HelperPath, throughIntermediate ? ["D5.S0.Carrier.Intermediate"] : [Target]),
            (IntermediatePath, ["D5.S0.Carrier.Further"]),
            (FurtherPath, [Target]),
            (UnrelatedPath, []),
        ];
        var baselineReport = Report(modules);
        var baseline = SyntheticFiles(modules[0].Imports);
        foreach (var module in modules.Skip(1))
        {
            baseline[module.Path] = ImportSource(module.Imports);
        }
        PinImporter(baseline, baselineReport);

        var candidate = new Dictionary<string, string>(baseline, StringComparer.Ordinal)
        {
            [changedPath] = ImportSource(candidateImports) + "-- candidate dependency\n",
        };
        var candidateReport = Report(modules.Select(module =>
            (module.Path, module.Path == changedPath ? candidateImports : module.Imports)).ToArray());
        Assert.Equal(new[] { changedPath }, baseline.Keys.Union(candidate.Keys)
            .Where(path => !baseline.TryGetValue(path, out var before)
                || !candidate.TryGetValue(path, out var after) || before != after)
            .Order(StringComparer.Ordinal));
        var changes = RawChangeSet.CreateWithKinds([(changedPath, RawChangeKind.Modified)]);

        // Evaluate each snapshot against the other: both runs have the exact same byte delta.
        // The baseline run checks restored reachability; no fabricated importer edit selects it.
        return (SyntheticContext(baseline, candidate, baselineReport, changes),
            SyntheticContext(candidate, baseline, candidateReport, changes));
    }

    private static string ImportSource(IEnumerable<string> imports) =>
        string.Concat(imports.Select(import => $"import {import}\n")) + "-- dependency fixture\n";

    private static void AssertPairedAnchorChecks(
        DeltaRuleContext baseline,
        DeltaRuleContext candidate,
        string changedPath,
        bool affected,
        bool reachableAfter)
    {
        var importer = RepoPath.CreateKnown(RuleFixture.RingPath);
        Assert.Equal(baseline.Current.Files[importer].RawBytes.ToArray(),
            candidate.Current.Files[importer].RawBytes.ToArray());
        foreach (var context in new[] { baseline, candidate })
        {
            var change = Assert.Single(context.Changes.Entries);
            Assert.Equal(changedPath, change.Path.Value);
            Assert.Equal(RawChangeKind.Modified, change.Kind);
            Assert.Equal(affected, RepositoryRules.IsLeanClosureFactAffected(context, importer));
            Assert.Equal(affected, LeanImportClosure.RepositoryPaths(context.Lean.Report, importer)
                .Contains(RepoPath.CreateKnown(changedPath)));
        }

        Assert.True(LeanImportClosure.ImportsExternalModule(
            baseline.Lean.Report, LeanImportClosure.ModuleName(importer), Target));
        Assert.Equal(reachableAfter, LeanImportClosure.ImportsExternalModule(
            candidate.Lean.Report, LeanImportClosure.ModuleName(importer), Target));
        var before = ExecuteContext(baseline);
        var after = ExecuteContext(candidate);
        Assert.Contains(RuleId.CreateKnown(17), before.ExecutedRules);
        Assert.Contains(RuleId.CreateKnown(17), after.ExecutedRules);
        Assert.Empty(AnchorDiagnostics(before));
        if (reachableAfter)
        {
            Assert.Empty(AnchorDiagnostics(after));
        }
        else
        {
            AssertAnchorFinding(after);
        }
    }

    // Synthetic snapshots and policy: these applicability tests do not read repository data.
    private static CompletedRuleSet ExecuteDelta(
        string changedPath,
        bool added = false,
        bool directImport = false)
    {
        var ringImports = directImport ? new[] { Target } : new[] { "D5.S0.Carrier.Helper" };
        var report = Report(
            (RuleFixture.RingPath, ringImports),
            (HelperPath, []),
            (UnrelatedPath, []));
        var current = SyntheticFiles(ringImports);
        if (!added)
        {
            PinImporter(current, report);
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

        var changes = RawChangeSet.CreateWithKinds(
            [(changedPath, added ? RawChangeKind.Added : RawChangeKind.Modified)]);
        return ExecuteContext(SyntheticContext(current, baseline, report, changes));
    }

    private static DeltaRuleContext SyntheticContext(
        IReadOnlyDictionary<string, string> current,
        IReadOnlyDictionary<string, string> baseline,
        LeanAxiomReport report,
        RawChangeSet changes)
    {
        var policy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(TestFileMap.Canonical),
            Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;
        var context = DeltaRuleContext.Create(
            SyntheticSnapshot(current),
            SyntheticSnapshot(baseline),
            policy,
            AcceptedLeanClosure.Create(report),
            changes,
            MetaClear.Create());
        Assert.False(context.RuleImplementationChanged);
        return context;
    }

    private static CompletedRuleSet ExecuteContext(DeltaRuleContext context)
    {
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
