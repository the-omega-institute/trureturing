using System.Collections.Immutable;
using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed class RegistrationImportDirectionTests
{
    private const string Source = "D5/S0/Carrier/Source.lean";
    private const string Other = "D5/S0/Carrier/Other.lean";
    private const string Judge = "LeanInformationAudit.Syntax";
    private const string Analysis = "LeanInformationAuditAnalysis.Root";

    [Theory]
    [InlineData("LeanInformationAudit")]
    [InlineData(Judge)]
    [InlineData("LeanInformationAuditAnalysis")]
    [InlineData(Analysis)]
    [InlineData("LeanInformationAuditInterface")]
    [InlineData("LeanInformationAuditInterface.Syntax")]
    [InlineData("Reg")]
    [InlineData("Reg.D5.S0.Carrier.Source")]
    public void NewEdgeInCleanModuleBlocks(string module)
    {
        // Keep debt elsewhere to exercise the nonempty-base subset check.
        var baseline = Files((Other, Imports(Judge)), (Source, "-- clean\n"));
        var head = new Dictionary<string, string>(baseline) { [Source] = Imports(module) };
        AssertNewEdge(Evaluate(baseline, head, Reports((Other, [Judge]), (Source, [module]))), Source, module);
    }

    [Fact]
    public void NewEdgeInAlreadyIndebtedModuleBlocks()
    {
        AssertNewEdge(Evaluate(Files((Source, Imports(Judge))),
            Files((Source, Imports(Judge, Analysis))), Reports((Source, [Judge, Analysis]))), Source, Analysis);
    }

    [Fact]
    public void EqualSizeSubstitutionBlocks()
    {
        AssertNewEdge(Evaluate(Files((Source, Imports(Judge))),
            Files((Source, Imports(Analysis))), Reports((Source, [Analysis]))), Source, Analysis);
    }

    [Fact]
    public void SmallerDebtWithReplacementStillBlocks()
    {
        const string replacement = "Reg.Support.New";
        AssertNewEdge(Evaluate(Files((Source, Imports(Judge, Analysis))),
            Files((Source, Imports(replacement))), Reports((Source, [replacement]))), Source, replacement);
    }

    [Fact]
    public void MovingAnEdgeToAnotherModuleBlocks()
    {
        AssertNewEdge(Evaluate(Files((Source, Imports(Judge))),
            Files((Other, Imports(Judge))), Reports((Other, [Judge]))), Other, Judge);
    }

    [Fact]
    public void EqualSizeSubstitutionAcrossModulesBlocks()
    {
        // The old source strictly shrinks while a clean source gains its removed
        // edge. A global count check and the per-source reduction both allow this.
        AssertNewEdge(Evaluate(Files((Source, Imports(Judge, Analysis))),
            Files((Source, Imports(Judge)), (Other, Imports(Analysis))),
            Reports((Source, [Judge]), (Other, [Analysis]))), Other, Analysis);
    }

    [Fact]
    public void UntouchedIndebtedModulePasses()
    {
        var files = Files((Source, Imports(Judge)));
        AssertNoBlock(Evaluate(files, new(files), Reports((Source, [Judge]))));
    }

    [Fact]
    public void ByteIdenticalDebtPassesEvenWithChangedPathSignal()
    {
        var files = Files((Source, Imports(Judge)));
        AssertNoBlock(Evaluate(files, new(files), Reports((Source, [Judge])), [Source]));
    }

    [Fact]
    public void TouchedIndebtedModuleKeepingDebtBlocks()
    {
        var baseline = Files((Source, Imports(Judge)));
        var head = new Dictionary<string, string>(baseline) { [Source] = Imports(Judge) + "-- edited\n" };
        Assert.Contains(Evaluate(baseline, head, Reports((Source, [Judge]))), d =>
            d.Path == Source && d.AdmissionEffect == AdmissionEffect.Block
            && d.Message.Contains("must strictly reduce", StringComparison.Ordinal));
    }

    [Fact]
    public void ReductionElsewhereDoesNotExcuseTouchedDebt()
    {
        Assert.Contains(Evaluate(Files((Source, Imports(Judge, Analysis)), (Other, Imports(Judge))),
            Files((Source, Imports(Judge)), (Other, Imports(Judge) + "-- edited\n")),
            Reports((Source, [Judge]), (Other, [Judge]))), d =>
                d.Path == Other && d.AdmissionEffect == AdmissionEffect.Block
                && d.Message.Contains("must strictly reduce", StringComparison.Ordinal));
    }

    [Fact]
    public void ReorderingDebtDoesNotCountAsReduction()
    {
        Assert.Contains(Evaluate(Files((Source, Imports(Judge, Analysis))),
            Files((Source, Imports(Analysis, Judge))), Reports((Source, [Analysis, Judge]))), d =>
                d.AdmissionEffect == AdmissionEffect.Block && d.Message.Contains("must strictly reduce", StringComparison.Ordinal));
    }

    [Fact]
    public void RemovingDuplicateImportDoesNotReduceDebt()
    {
        Assert.Contains(Evaluate(Files((Source, Imports(Judge, Judge))),
            Files((Source, Imports(Judge))), Reports((Source, [Judge]))), d =>
                d.AdmissionEffect == AdmissionEffect.Block && d.Message.Contains("must strictly reduce", StringComparison.Ordinal));
    }

    [Fact]
    public void TouchedModuleRemovingOneOfTwoEdgesPasses()
    {
        AssertNoBlock(Evaluate(Files((Source, Imports(Judge, Analysis))),
            Files((Source, Imports(Judge))), Reports((Source, [Judge]))));
    }

    [Fact]
    public void DeletingIndebtedModulePasses()
    {
        AssertNoBlock(Evaluate(Files((Source, Imports(Judge))), Files(), Reports()));
    }

    [Fact]
    public void EmptyBaseDebtJudgesFullTreeEvenOutsideChangedPaths()
    {
        AssertNewEdge(Evaluate(Files((Source, "-- clean\n")),
            Files((Source, Imports(Judge))), Reports((Source, [Judge])), ["docs/Unrelated.md"]), Source, Judge);
    }

    [Theory]
    [InlineData("Reg.lean")]
    [InlineData("Reg/D5/S0/Carrier/Source.lean")]
    public void RegImportingD5AndJudgePasses(string registration)
    {
        // Include the downstream report entry too: Reg is not a D5 stratum.
        AssertNoBlock(Evaluate(Files((Source, "-- math\n")),
            Files((Source, "-- math\n"), (registration, Imports("D5.S0.Carrier.Source", Judge))),
            Reports((Source, []), (registration, ["D5.S0.Carrier.Source", Judge]))));
    }

    [Fact]
    public void ExistingD5StratumViolationIsStillReported()
    {
        const string higher = "D5/S1/Phase/Higher.lean";
        var files = Files((Source, Imports("D5.S1.Phase.Higher")), (higher, "-- math\n"));
        Assert.Contains(Evaluate(files, new(files), Reports((Source, ["D5.S1.Phase.Higher"]), (higher, []))), d =>
            d.AdmissionEffect == AdmissionEffect.Block && d.Message == $"stratum closure may not import {higher}");
    }

    [Fact]
    public void SimilarNamespacePrefixesAreNotForbidden()
    {
        string[] modules = ["Regular.Math", "RegExtra", "LeanInformationAuditExtra.Syntax"];
        AssertNoBlock(Evaluate(Files(), Files((Source, Imports(modules))), Reports((Source, modules))));
    }

    [Fact]
    public void BaseCommentsAndStringsDoNotGrantDebt()
    {
        var text = $"/- import {Judge} -/\ndef text := \"import {Judge}\"\n";
        AssertNewEdge(Evaluate(Files((Source, text)), Files((Source, Imports(Judge))),
            Reports((Source, [Judge]))), Source, Judge);
    }

    [Fact]
    public void BaseMultilineImportsAndNestedCommentsPreserveDebt()
    {
        var text = $"/- outer /- import Reg.Fake -/ -/\nimport\n  {Judge}\nimport\n  {Analysis}\n";
        AssertNoBlock(Evaluate(Files((Source, text)), Files((Source, Imports(Judge))), Reports((Source, [Judge]))));
    }

    [Fact]
    public void BaseCommandAfterImportsDoesNotGrantDebt()
    {
        var text = $"import Mathlib\n#check {Judge}\n";
        AssertNewEdge(Evaluate(Files((Source, text)), Files((Source, Imports(Judge))),
            Reports((Source, [Judge]))), Source, Judge);
    }

    [Theory]
    [InlineData("public import")]
    [InlineData("meta import")]
    [InlineData("public meta import")]
    [InlineData("import all")]
    public void BaseModuleImportModifiersPreserveDebt(string command)
    {
        var text = $"module\n{command} {Judge}\n";
        var files = Files((Source, text));
        AssertNoBlock(Evaluate(files, new(files), Reports((Source, [Judge]))));
    }

    [Theory]
    [InlineData("«LeanInformationAudit».Syntax")]
    [InlineData("LeanInformationAudit.«Syntax»")]
    [InlineData("«LeanInformationAudit».«Syntax»")]
    public void BaseQuotedModuleIdentifiersPreserveDebt(string module)
    {
        var files = Files((Source, Imports(module)));
        AssertNoBlock(Evaluate(files, new(files), Reports((Source, [Judge]))));
    }

    [Fact]
    public void QuotedDifferentRootDoesNotGrantDebt()
    {
        AssertNewEdge(Evaluate(Files((Source, Imports("«LeanInformation Audit».Syntax"))),
            Files((Source, Imports(Judge))), Reports((Source, [Judge]))), Source, Judge);
    }

    [Theory]
    [InlineData(Source, true)]
    [InlineData("tools/lean-inspector/Inspector.lean", true)]
    [InlineData("lean-report-inputs.json", true)]
    [InlineData("lake-manifest.json", true)]
    [InlineData("Blueprint/D5/S0/Carrier/Source.md", false)]
    public void RegistrationDeltaDeclaresSourceAndReportInputClosure(string path, bool affected)
    {
        var rule = RepositoryRules.CreateRegistrations().Single(r => r.Descriptor.Id == RuleId.CreateKnown(1)).Rule;
        Assert.Equal(affected, rule.IsAffectedBy(Context(Files(), Files(), Reports(), [path])));
    }

    private static string Imports(params string[] modules) =>
        string.Concat(modules.Select(module => $"import {module}\n"));

    private static Dictionary<string, string> Files(params (string Path, string Text)[] files) =>
        files.ToDictionary(item => item.Path, item => item.Text, StringComparer.Ordinal);

    private static LeanAxiomReport Reports(params (string Path, string[] Imports)[] files) =>
        LeanAxiomReport.Create(files.ToDictionary(item => item.Path,
            item => new LeanFileReport(item.Imports.ToImmutableArray(), []), StringComparer.Ordinal));

    private static ImmutableArray<Diagnostic> Evaluate(Dictionary<string, string> baseline,
        Dictionary<string, string> head, LeanAxiomReport report, string[]? changedPaths = null)
        => RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(1),
            Context(baseline, head, report, changedPaths)).Diagnostics;

    private static DeltaRuleContext Context(Dictionary<string, string> baseline,
        Dictionary<string, string> head, LeanAxiomReport report, string[]? changedPaths = null)
    {
        var registration = EngineeringRegistrationFixture.Manifest();
        baseline[EngineeringRegistrationFixture.Path] = registration;
        head[EngineeringRegistrationFixture.Path] = registration;
        var changes = RawChangeSet.Create(changedPaths ?? baseline.Keys.Union(head.Keys)
            .Where(path => baseline.GetValueOrDefault(path) != head.GetValueOrDefault(path)));
        var policy = ValidatedPolicy.Create([], [], [], ImmutableDictionary<DomainId, Stratum>.Empty,
            ImmutableDictionary<ArtifactKindId, ArtifactPolicy>.Empty, [], []);
        var meta = BootstrapGate.Evaluate(changes) switch
        {
            BootstrapOutcome.Clear clear => MetaEvaluationProfile.ForClear(clear.Capability),
            BootstrapOutcome.ProtectedSurfaceVerificationRequired required =>
                MetaEvaluationProfile.ForProtectedSurface(required.ChangeSet),
            _ => throw new InvalidOperationException("invalid synthetic bootstrap"),
        };
        return DeltaRuleContext.Create(Tree(head), Tree(baseline), policy,
            AcceptedLeanClosure.Create(report), changes, meta);
    }

    private static RepositorySnapshot Tree(Dictionary<string, string> files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            files.Select(item => RawRepositoryEntry.FromText(item.Key, item.Value))))).Snapshot;

    private static void AssertNewEdge(IEnumerable<Diagnostic> diagnostics, string path, string module) =>
        Assert.Contains(diagnostics, d => d.RuleId == RuleId.CreateKnown(1) && d.Path == path
            && d.AdmissionEffect == AdmissionEffect.Block
            && d.Message == $"D5 may not add forbidden import {module}");

    private static void AssertNoBlock(IEnumerable<Diagnostic> diagnostics) =>
        Assert.DoesNotContain(diagnostics, d => d.AdmissionEffect == AdmissionEffect.Block);
}
