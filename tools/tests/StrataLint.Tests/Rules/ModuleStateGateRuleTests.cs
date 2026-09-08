using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ModuleStateGateRuleTests
{
    private const string Rule = "SL-034";
    private const string ClosedPath = "D5/S0/Carrier/NewClosed.lean";
    private const string FrontierPath = "D5/X_Frontier/SyntheticOpen.lean";
    private const string TailPath = "D5/X_Assumptions/SyntheticTail.lean";
    private const string ImplementationPath = "tools/StrataLint.Engine/Rules/ModuleStateGateRule.cs";

    [Fact]
    public void AddedClosedModuleWithoutStateObservesAndNamesModule()
    {
        var fixture = new RuleFixture();
        AddModule(fixture, ClosedPath, "def newClosed : Nat := 0", []);

        var diagnostic = Assert.Single(Evaluate(
            fixture,
            (ClosedPath, RawChangeKind.Added)));

        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.NotEqual(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(ClosedPath, diagnostic.Path);
        Assert.Contains(ClosedPath, diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ObserveFindingDoesNotBlockAdmissionAndRemainsVisible()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        AddModule(fixture, ClosedPath, "def newClosed : Nat := 0", []);
        var changes = RawChangeSet.CreateWithKinds([(ClosedPath, RawChangeKind.Added)]);
        var context = fixture.Build(changes);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context)).Capability;
        var finding = Assert.Single(Diagnostics(completed));

        Assert.Equal(AdmissionEffect.Observe, finding.AdmissionEffect);
        Assert.NotEqual(AdmissionEffect.Block, finding.AdmissionEffect);
        Assert.Null(AdmissionEngine.RejectIfNeeded(completed, context.MetaEvaluation));

        var clear = Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(changes)).Capability;
        var admitted = Assert.IsType<AdmissionOutcome.Admitted>(AdmissionPipeline.Evaluate(
            context.Current, context.Baseline, context.Policy, context.Lean, changes, clear));
        var observation = Assert.Single(admitted.Observations,
            diagnostic => diagnostic.RuleId.Value == Rule);
        Assert.Equal(finding, observation);
        Assert.Equal(ClosedPath, observation.Path);
    }

    [Fact]
    public void AddedClosedModuleWithStateIsAllowed()
    {
        var fixture = new RuleFixture();
        AddModule(fixture, ClosedPath, "def newClosed : Nat := 0", []);
        AddState(fixture, ClosedPath);

        var completed = Execute(
            fixture,
            (ClosedPath, RawChangeKind.Added),
            (StatePath(ClosedPath), RawChangeKind.Added));

        Assert.Contains(completed.ExecutedRules, id => id.Value == Rule);
        Assert.Empty(Diagnostics(completed));
    }

    [Fact]
    public void AddedFrontierModuleWithoutStateIsAllowed()
    {
        var fixture = new RuleFixture();
        AddModule(fixture, FrontierPath, "def syntheticOpen : Nat := 0", []);

        Assert.Empty(Evaluate(fixture, (FrontierPath, RawChangeKind.Added)));
    }

    [Fact]
    public void AddedNonClosedModuleWithoutStateIsAllowed()
    {
        var fixture = new RuleFixture();
        AddModule(fixture, TailPath, "axiom syntheticTail : True", [
            new LeanDeclaration(
                "syntheticTail",
                "axiom",
                "True",
                ImmutableArray<string>.Empty),
        ]);

        Assert.Empty(Evaluate(fixture, (TailPath, RawChangeKind.Added)));
    }

    [Fact]
    public void ExistingUnfrozenBaselineModuleIsIgnoredWhenCandidateDoesNotTouchIt()
    {
        var fixture = new RuleFixture();
        AddModule(fixture, ClosedPath, "def existingClosed : Nat := 0", []);
        fixture.Baseline[ClosedPath] = fixture.Files[ClosedPath];
        fixture.BaselineReports[ClosedPath] = fixture.Reports[ClosedPath];
        fixture.Files["docs/new-note.md"] = "fixture\n";

        var completed = Execute(fixture, ("docs/new-note.md", RawChangeKind.Added));

        Assert.DoesNotContain(completed.ExecutedRules, id => id.Value == Rule);
        Assert.Empty(Diagnostics(completed));
    }

    [Fact]
    public void TenUnfrozenBaselineModulesAreIgnoredWhileAnotherModuleIsAdded()
    {
        var fixture = new RuleFixture();
        for (var index = 0; index < 10; index++)
        {
            AddBaselineModule(fixture, $"D5/S0/Carrier/ExistingClosed{index}.lean");
        }

        AddModule(fixture, ClosedPath, "def newClosed : Nat := 0", []);
        AddState(fixture, ClosedPath);
        var completed = Execute(fixture,
            (ClosedPath, RawChangeKind.Added),
            (StatePath(ClosedPath), RawChangeKind.Added));

        Assert.Contains(completed.ExecutedRules, id => id.Value == Rule);
        Assert.Empty(Diagnostics(completed));
    }

    [Fact]
    public void BaselineModuleReportedAsAddedIsIgnored()
    {
        var fixture = new RuleFixture();
        AddBaselineModule(fixture, ClosedPath);

        var completed = Execute(fixture, (ClosedPath, RawChangeKind.Added));

        Assert.DoesNotContain(completed.ExecutedRules, id => id.Value == Rule);
        Assert.Empty(Diagnostics(completed));
    }

    [Fact]
    public void ModifiedUnfrozenBaselineModuleIsIgnored()
    {
        var fixture = new RuleFixture();
        AddBaselineModule(fixture, ClosedPath);
        fixture.Files[ClosedPath] += "-- changed comment\n";

        var completed = Execute(fixture, (ClosedPath, RawChangeKind.Modified));

        Assert.DoesNotContain(completed.ExecutedRules, id => id.Value == Rule);
        Assert.Empty(Diagnostics(completed));
    }

    [Fact]
    public void RuleImplementationChangeDoesNotRecheckBaselineDebt()
    {
        var fixture = new RuleFixture();
        AddBaselineModule(fixture, ClosedPath);
        fixture.Files[ImplementationPath] = "// changed judge\n";
        var context = fixture.Build(RawChangeSet.Create([ImplementationPath]));
        Assert.True(context.RuleImplementationChanged);

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context)).Capability;

        Assert.DoesNotContain(completed.ExecutedRules, id => id.Value == Rule);
        Assert.Empty(Diagnostics(completed));
    }

    [Fact]
    public void AddedClosedModuleStillObservesWhenRuleImplementationChanges()
    {
        var fixture = new RuleFixture();
        AddModule(fixture, ClosedPath, "def newClosed : Nat := 0", []);
        fixture.Files[ImplementationPath] = "// changed judge\n";

        var diagnostic = Assert.Single(Evaluate(fixture,
            (ImplementationPath, RawChangeKind.Added),
            (ClosedPath, RawChangeKind.Added)));

        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.Equal(ClosedPath, diagnostic.Path);
        Assert.Contains(ClosedPath, diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AddedClosedModuleCannotUseStateRemovedFromCandidate()
    {
        var fixture = new RuleFixture();
        AddModule(fixture, ClosedPath, "def newClosed : Nat := 0", []);
        AddState(fixture, ClosedPath);
        var statePath = StatePath(ClosedPath);
        fixture.Baseline[statePath] = fixture.Files[statePath];
        fixture.Files.Remove(statePath);

        var diagnostic = Assert.Single(Evaluate(fixture,
            (ClosedPath, RawChangeKind.Added),
            (statePath, RawChangeKind.Deleted)));

        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.Equal(ClosedPath, diagnostic.Path);
        Assert.Contains(statePath, diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AddedOpenModuleOutsideFrontierIsAllowed()
    {
        var fixture = new RuleFixture();
        AddModule(fixture, ClosedPath, "-- TASK D5-T9999\ndef newOpen : Nat := 0", []);
        var context = fixture.Build(RawChangeSet.CreateWithKinds([(ClosedPath, RawChangeKind.Added)]));
        Assert.Equal(TruthState.Open,
            LeanTruthStates.Resolve(context.Current, context.Lean)[RepoPath.CreateKnown(ClosedPath)]);

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context)).Capability;

        Assert.Contains(completed.ExecutedRules, id => id.Value == Rule);
        Assert.Empty(Diagnostics(completed));
    }

    [Fact]
    public void MalformedAddedModulePathObservesWithoutInfrastructureFailure()
    {
        const string malformed = "D5/s0/Carrier/Bad.lean";
        var fixture = new RuleFixture();
        AddModule(fixture, malformed, "def bad : Nat := 0", []);
        var context = fixture.BuildForRuleCompatibility(
            RawChangeSet.CreateWithKinds([(malformed, RawChangeKind.Added)]));

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context)).Capability;
        var diagnostic = Assert.Single(Diagnostics(completed));

        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.Equal(malformed, diagnostic.Path);
        Assert.Contains("MODULE_STATE_INPUT_INVALID", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(malformed, diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    [BaseFactScopeProbe(34)]
    public void Sl034ScopesCandidateWithoutD5Module()
    {
        var fixture = new RuleFixture();
        fixture.Files["docs/new-note.md"] = "fixture\n";

        var completed = Execute(fixture, ("docs/new-note.md", RawChangeKind.Added));

        Assert.DoesNotContain(completed.ExecutedRules, id => id.Value == Rule);
        Assert.Empty(Diagnostics(completed));
    }

    [Fact]
    public void ModuleStateGateIsRegisteredAsActiveAndObserving()
    {
        var descriptor = Assert.Single(RuleCatalog.Default.Descriptors, item => item.Id.Value == Rule);
        Assert.Equal(AdmissionEffect.Observe, descriptor.AdmissionEffect);
        Assert.Equal(RuleLifecycle.Active, descriptor.Lifecycle);
        Assert.Equal("Closed Lean modules missing frozen state", descriptor.Title);
    }

    private static void AddModule(
        RuleFixture fixture,
        string path,
        string declaration,
        IEnumerable<LeanDeclaration> declarations)
    {
        var gid = path[..^".lean".Length];
        fixture.Files[path] = $"/- GID: {gid}\n"
            + "   generality: G\n"
            + "   mirror-B: none(waiver:test-fixture)\n"
            + "   mirror-E: none(waiver:test-fixture)\n"
            + "   anchors: []\n"
            + "   utility: none\n"
            + "   digest: StrataLint fixture. -/\n"
            + declaration + "\n";
        fixture.Reports[path] = new LeanFileReport(
            ImmutableArray<string>.Empty,
            declarations.ToImmutableArray());
    }

    private static void AddState(RuleFixture fixture, string modulePath)
    {
        var statePath = StatePath(modulePath);
        fixture.Files[statePath] = "{\"statement_id\":\"sha256:"
            + new string('0', 64)
            + "\"}\n";
    }

    private static void AddBaselineModule(RuleFixture fixture, string path)
    {
        AddModule(fixture, path, "def existingClosed : Nat := 0", []);
        fixture.Baseline[path] = fixture.Files[path];
        fixture.BaselineReports[path] = fixture.Reports[path];
    }

    private static string StatePath(string modulePath) =>
        "Golden/Frozen/state/" + modulePath + ".json";

    private static ImmutableArray<Diagnostic> Diagnostics(CompletedRuleSet completed) =>
        completed.Diagnostics
            .Where(diagnostic => diagnostic.RuleId.Value == Rule)
            .ToImmutableArray();

    private static ImmutableArray<Diagnostic> Evaluate(
        RuleFixture fixture,
        params (string Path, RawChangeKind Kind)[] changes) =>
        Diagnostics(Execute(fixture, changes));

    private static CompletedRuleSet Execute(
        RuleFixture fixture,
        params (string Path, RawChangeKind Kind)[] changes) =>
        Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(
            fixture.Build(RawChangeSet.CreateWithKinds(changes)))).Capability;
}
