using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class NativeDecideAdmissionTests
{
    private const string Path = "D5/S0/Carrier/Anonymous.lean";

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void EqualityAmbiguityProductionAdmissionAcceptsSelectedOrUnchangedSource(bool historical, bool spaced)
    {
        var source = FirstOrderEqualitySource(spaced);
        var context = Candidate("decide", historical ? "" : source, historical ? source : null,
            sourceImport: "Mathlib.ModelTheory.Syntax");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-008");
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        Assert.DoesNotContain(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
        Assert.IsType<AdmissionOutcome.Admitted>(Admit(context));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualityAmbiguityProductionAdmissionRejectsFollowingNativeDecide(bool spaced)
    {
        var context = Candidate("native_decide", FirstOrderEqualitySource(spaced),
            sourceImport: "Mathlib.ModelTheory.Syntax");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        var diagnostic = Assert.Single(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
        Assert.Equal("SL-035", diagnostic.RuleId.Value);
        Assert.Equal(Path, diagnostic.Path);
        Assert.Equal("NATIVE_DECIDE_SOURCE line=12: bare native_decide token is forbidden in changed D5 Lean source", diagnostic.Message);
        Assert.Contains(diagnostic, Assert.IsType<AdmissionOutcome.RuleRejected>(Admit(context)).Diagnostics);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualityAmbiguityProductionAdmissionAcceptsRealCharacters(bool historical)
    {
        const string source = "example : 'g' ='g' := by rfl\n";
        var context = Candidate("decide", historical ? "" : source, historical ? source : null, sourceImport: "Init");
        Assert.IsType<AdmissionOutcome.Admitted>(Admit(context));
    }

    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, false, true)]
    [InlineData(false, true, false)]
    [InlineData(false, true, true)]
    [InlineData(true, false, false)]
    [InlineData(true, false, true)]
    [InlineData(true, true, false)]
    [InlineData(true, true, true)]
    public void EqualityContextProductionAdmissionKeepsWholeNamesAndFollowingBareToken(bool qualified, bool spaced, bool bare)
    {
        var context = Candidate(bare ? "native_decide" : "decide", EqualitySpanSource(qualified, spaced),
            sourceImport: "Mathlib.ModelTheory.Syntax");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        if (!bare)
        {
            Assert.DoesNotContain(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
            Assert.IsType<AdmissionOutcome.Admitted>(Admit(context));
            return;
        }

        var diagnostic = Assert.Single(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
        Assert.Equal("SL-035", diagnostic.RuleId.Value);
        Assert.Equal(Path, diagnostic.Path);
        Assert.Equal($"NATIVE_DECIDE_SOURCE line={(qualified ? 13 : 12)}: bare native_decide token is forbidden in changed D5 Lean source", diagnostic.Message);
        Assert.Contains(diagnostic, Assert.IsType<AdmissionOutcome.RuleRejected>(Admit(context)).Diagnostics);
    }

    private static string EqualitySpanSource(bool qualified, bool spaced)
    {
        var source = FirstOrderEqualitySource(spaced);
        if (!qualified)
        {
            return source.Replace("g'", "g'native_decide", StringComparison.Ordinal);
        }

        return source.Replace("example (t g' :", "def g'.native_decide : FirstOrder.Language.Term FirstOrder.Language.empty (Sum Nat (Fin 0)) := .var (.inl 0)\nexample (t :", StringComparison.Ordinal)
            .Replace("g')", "g'.native_decide)", StringComparison.Ordinal);
    }

    private static string FirstOrderEqualitySource(bool spaced) =>
        "import Mathlib.ModelTheory.Syntax\nopen scoped FirstOrder\n"
        + "example (t g' : FirstOrder.Language.Term FirstOrder.Language.empty (Sum Nat (Fin 0))) :\n"
        + $"    (t ='{(spaced ? " " : "")}g') = (t ='{(spaced ? " " : "")}g') := by rfl\n";

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void ProductionAdmissionAcceptsDependentCompositionInSelectedOrUnchangedSource(bool historical, bool spaced)
    {
        var source = DependentCompositionSource(spaced);
        var context = Candidate("decide", historical ? "" : source, historical ? source : null,
            sourceImport: "Mathlib.Logic.Function.Defs");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-008");
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        Assert.DoesNotContain(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
        Assert.IsType<AdmissionOutcome.Admitted>(Admit(context));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProductionAdmissionRejectsNativeDecideFollowingDependentComposition(bool spaced)
    {
        var context = Candidate("native_decide", DependentCompositionSource(spaced),
            sourceImport: "Mathlib.Logic.Function.Defs");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        var diagnostic = Assert.Single(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
        Assert.Equal("SL-035", diagnostic.RuleId.Value);
        Assert.Equal(Path, diagnostic.Path);
        Assert.Equal("NATIVE_DECIDE_SOURCE line=10: bare native_decide token is forbidden in changed D5 Lean source", diagnostic.Message);
        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(Admit(context));
        Assert.Contains(diagnostic, rejected.Diagnostics);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProductionAdmissionAcceptsOrdinaryCompositionControl(bool historical)
    {
        var source = DependentCompositionSource(spaced: true).Replace("\u2218'", "\u2218", StringComparison.Ordinal);
        var context = Candidate("decide", historical ? "" : source, historical ? source : null,
            sourceImport: "Mathlib.Logic.Function.Defs");
        Assert.IsType<AdmissionOutcome.Admitted>(Admit(context));
    }

    private static string DependentCompositionSource(bool spaced) =>
        "import Mathlib.Logic.Function.Defs\n"
        + $"example (f g' : Nat -> Nat) : (f \u2218'{(spaced ? " " : "")}g') = (f \u2218 g') := rfl\n";

    [Fact]
    public void ProductionAdmissionRejectsAnonymousNativeDecideWithEmptyReport()
    {
        var context = Candidate("native_decide");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        var diagnostic = Assert.Single(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
        Assert.Equal("SL-035", diagnostic.RuleId.Value);
        Assert.Equal(Path, diagnostic.Path);
        Assert.Equal("NATIVE_DECIDE_SOURCE line=8: bare native_decide token is forbidden in changed D5 Lean source", diagnostic.Message);
        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(Admit(context));
        Assert.Contains(diagnostic, rejected.Diagnostics);
    }

    [Fact]
    public void ProductionAdmissionAcceptsPairedKernelDecideWithEmptyReport()
    {
        var context = Candidate("decide");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        Assert.DoesNotContain(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
        Assert.IsType<AdmissionOutcome.Admitted>(Admit(context));
    }

    [Theory]
    [InlineData("\u2211'", false)]
    [InlineData("\u220f'", false)]
    [InlineData("\u2211'", true)]
    [InlineData("\u220f'", true)]
    public void ProductionAdmissionAcceptsPrimeNotationInSelectedOrUnchangedSource(string notation, bool historical)
    {
        var source = "import Mathlib.Topology.Algebra.InfiniteSum.Defs\n"
            + $"example (f : Nat -> Nat) : ({notation} n, f n) = ({notation} n, f n) := rfl\n";
        var context = Candidate("decide", historical ? string.Empty : source, historical ? source : null);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;

        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-008");
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        Assert.DoesNotContain(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
        Assert.IsType<AdmissionOutcome.Admitted>(Admit(context));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProductionAdmissionAcceptsImageNotationInSelectedOrUnchangedSource(bool historical)
    {
        const string source = "import Mathlib.Data.Set.Image\n"
            + "example (f : Nat -> Nat) (s : Set Nat) : f '' s = f '' s := rfl\n";
        var context = Candidate("decide", historical ? string.Empty : source, historical ? source : null,
            sourceImport: "Mathlib.Data.Set.Image");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;

        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-008");
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        Assert.DoesNotContain(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
        Assert.IsType<AdmissionOutcome.Admitted>(Admit(context));
    }

    [Fact]
    public void ProductionAdmissionRejectsNativeDecideFollowingImageNotation()
    {
        const string source = "import Mathlib.Data.Set.Image\n"
            + "example (f : Nat -> Nat) (s : Set Nat) : f '' s = f '' s := rfl\n";
        var context = Candidate("native_decide", source, sourceImport: "Mathlib.Data.Set.Image");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        var diagnostic = Assert.Single(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
        Assert.Equal("SL-035", diagnostic.RuleId.Value);
        Assert.Equal(Path, diagnostic.Path);
        Assert.Equal("NATIVE_DECIDE_SOURCE line=10: bare native_decide token is forbidden in changed D5 Lean source", diagnostic.Message);
        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(Admit(context));
        Assert.Contains(diagnostic, rejected.Diagnostics);
    }

    private static RuleEvaluationContext Candidate(string tactic, string prefix = "", string? historicalSource = null,
        string sourceImport = "Mathlib.Topology.Algebra.InfiniteSum.Defs")
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[Path] = "/- GID: D5/S0/Carrier/Anonymous\n"
            + "   generality: G\n"
            + "   mirror-B: none(waiver:test-fixture)\n"
            + "   mirror-E: none(waiver:test-fixture)\n"
            + "   anchors: []\n"
            + "   utility: none\n"
            + "   digest: Anonymous source admission fixture. -/\n"
            + prefix
            + $"example : True := by {tactic}\n";
        fixture.Reports[Path] = new LeanFileReport(
            prefix.Length == 0 ? [] : [sourceImport], []);
        if (historicalSource is not null)
        {
            fixture.Files[RuleFixture.RingPath] = historicalSource + fixture.Files[RuleFixture.RingPath];
            fixture.Baseline[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath];
            fixture.Reports[RuleFixture.RingPath] = fixture.Reports[RuleFixture.RingPath] with
            {
                Imports = [sourceImport],
            };
            fixture.BaselineReports[RuleFixture.RingPath] = fixture.Reports[RuleFixture.RingPath];
        }
        Assert.Empty(fixture.Reports[Path].Declarations);
        var context = fixture.Build(RawChangeSet.CreateWithKinds([(Path, RawChangeKind.Added)]));
        return RuleEvaluationContext.Create(context.Current, context.Baseline, context.Policy, context.Lean,
            context.Changes, context.MetaEvaluation, context.VerifiedScribeEmissions,
            sourceContext: SyntheticSourceContext.ForSnapshots(context.Current, context.Baseline));
    }

    private static AdmissionOutcome Admit(RuleEvaluationContext context) => AdmissionPipeline.EvaluateWithScribe(
        context.Current, context.Baseline, context.Policy, context.Lean, context.Changes,
        Assert.IsType<BootstrapOutcome.Clear>(BootstrapGate.Evaluate(context.Changes)).Capability,
        context.VerifiedScribeEmissions, sourceContext: context.SourceContext);
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Repair7IndentedOpenAcceptsLongerNameThroughCatalog(bool indented)
    {
        var source = EqualitySpanSource(qualified: false, spaced: false)
            .Replace("\nopen scoped", indented ? "\n open scoped" : "\nopen scoped", StringComparison.Ordinal);
        var context = Candidate("decide", source, sourceImport: "Mathlib.ModelTheory.Syntax");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        Assert.DoesNotContain(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Repair7IndentedOpenAcceptsLongerNameThroughAdmission(bool indented)
    {
        var source = EqualitySpanSource(qualified: false, spaced: false)
            .Replace("\nopen scoped", indented ? "\n open scoped" : "\nopen scoped", StringComparison.Ordinal);
        var context = Candidate("decide", source, sourceImport: "Mathlib.ModelTheory.Syntax");
        Assert.IsType<AdmissionOutcome.Admitted>(Admit(context));
    }

    [Theory]
    [InlineData("FirstOrder")]
    [InlineData("Ordinary")]
    public void Repair7InitOnlyCharAcceptsKernelDecideThroughCatalog(string ns)
    {
        var source = $"import Init\nnamespace {ns}\ndef g' : Nat := 0\nend {ns}\nopen {ns}\n"
            + "example : ')' =')' := by decide\n";
        var context = Candidate("decide", source, sourceImport: "Init");
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;
        Assert.Contains(completed.ExecutedRules, id => id.Value == "SL-035");
        Assert.DoesNotContain(completed.Diagnostics, item => item.AdmissionEffect == AdmissionEffect.Block);
    }

    [Theory]
    [InlineData("FirstOrder")]
    [InlineData("Ordinary")]
    public void Repair7InitOnlyCharAcceptsKernelDecideThroughAdmission(string ns)
    {
        var source = $"import Init\nnamespace {ns}\ndef g' : Nat := 0\nend {ns}\nopen {ns}\n"
            + "example : ')' =')' := by decide\n";
        var context = Candidate("decide", source, sourceImport: "Init");
        Assert.IsType<AdmissionOutcome.Admitted>(Admit(context));
    }

}
