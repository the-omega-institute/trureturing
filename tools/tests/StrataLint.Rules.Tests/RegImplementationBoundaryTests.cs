using StrataLint.Configuration;
using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Rules.Tests;

public sealed class RegImplementationBoundaryTests
{
    private const string Lakefile = "Reg/lakefile.toml";
    private const string Source = "Reg/Source.lean";
    private const string Judge = "LeanInformationAudit.Syntax";
    private const string OtherJudge = "LeanInformationAudit.SealCommand";
    private const string Config = """
        name = "reg"
        defaultTargets = ["Reg"]
        [[lean_lib]]
        name = "Reg"
        srcDir = ".."
        roots = ["Reg"]
        globs = ["Reg.+"]
        """;

    [Fact]
    public void DirectImplementationImportBlocksWithoutReportEntry()
    {
        var baseline = Files();
        var head = Files((Source, $"import {Judge}\n"));
        AssertBlock(Evaluate(baseline, head), Source, Judge);
    }

    [Theory]
    [InlineData("Reg.Support.Helper", "Reg/Support/Helper.lean")]
    [InlineData("LeanInformationAuditInterface.Helper", "tools/lean-inspector-interface/LeanInformationAuditInterface/Helper.lean")]
    public void TransitiveImplementationImportBlocks(string module, string path)
    {
        var head = Files((Source, $"import {module}\n"), (path, $"import {Judge}\n"));
        AssertBlock(Evaluate(Files(), head), path, Judge);
    }

    [Fact]
    public void NonDefaultLibraryIsPartOfRegPackage()
    {
        var head = Files(("tools/lean-inspector/Extra/Probe.lean", $"import {Judge}\n"));
        head[Lakefile] += "\n[[lean_lib]]\nname = \"Extra\"\nsrcDir = \"../tools/lean-inspector\"\nglobs = [\"Extra.+\"]\n";
        AssertBlock(Evaluate(Files(), head), "tools/lean-inspector/Extra/Probe.lean", Judge);
    }

    [Fact]
    public void ImplementationRequireBlocks()
    {
        var head = Files();
        head[Lakefile] += "\n[[require]]\nname = \"leanInspector\"\npath = \"../tools/lean-inspector\"\n";
        AssertBlock(Evaluate(Files(), head), Lakefile, "leanInspector");
    }

    [Fact]
    public void RenamedImplementationRequireBlocks()
    {
        var head = Files();
        head[Lakefile] += "\n[[require]]\nname = \"renamed\"\npath = \"../tools/lean-inspector\"\n";
        AssertBlock(Evaluate(Files(), head), Lakefile, "tools/lean-inspector");
    }

    [Fact]
    public void ImplementationDefaultTargetBlocks()
    {
        var head = Files();
        head[Lakefile] = Config.Replace("[\"Reg\"]", "[\"Reg\", \"LeanInformationAuditRegTests\"]", StringComparison.Ordinal);
        AssertBlock(Evaluate(Files(), head), Lakefile, "LeanInformationAuditRegTests");
    }

    [Fact]
    public void UntouchedDebtPassesWithObserve()
    {
        var baseline = Files((Source, $"import {Judge}\n"));
        var result = Evaluate(baseline, new(baseline));
        AssertNoBlock(result);
        Assert.Contains(result, d => d.AdmissionEffect == AdmissionEffect.Observe && d.Path == Source);
    }

    [Fact]
    public void TouchedDebtMustStrictlyShrink()
    {
        var baseline = Files((Source, $"import {Judge}\n"));
        var head = new Dictionary<string, string>(baseline) { [Source] = baseline[Source] + "-- change\n" };
        AssertBlock(Evaluate(baseline, head), Source, "strictly reduce");
    }

    [Fact]
    public void EqualCountSubstitutionBlocks()
    {
        AssertBlock(Evaluate(Files((Source, $"import {Judge}\n")),
            Files((Source, $"import {OtherJudge}\n"))), Source, OtherJudge);
    }

    [Fact]
    public void SmallerDebtCannotIntroduceReplacement()
    {
        var baseline = Files((Source, $"import {Judge}\nimport {OtherJudge}\n"));
        AssertBlock(Evaluate(baseline, Files((Source, "import LeanInformationAudit.Registry\n"))),
            Source, "LeanInformationAudit.Registry");
    }

    [Fact]
    public void MovingDebtToAnotherModuleBlocks()
    {
        AssertBlock(Evaluate(Files((Source, $"import {Judge}\n")),
            Files(("Reg/Moved.lean", $"import {Judge}\n"))), "Reg/Moved.lean", Judge);
    }

    [Fact]
    public void StrictReductionPasses()
    {
        AssertNoBlock(Evaluate(Files((Source, $"import {Judge}\nimport {OtherJudge}\n")),
            Files((Source, $"import {Judge}\n"))));
    }

    [Fact]
    public void CleanBaseChecksWholePackageOutsideDelta()
    {
        AssertBlock(Evaluate(Files(), Files((Source, $"import {Judge}\n")), ["docs/Unrelated.md"]), Source, Judge);
    }

    [Fact]
    public void InterfaceMathlibAndD5DependenciesPass()
    {
        var head = Files((Source, "import D5.S0.Carrier.Source\nimport Mathlib\nimport LeanInformationAuditInterface.Syntax\n"),
            ("D5/S0/Carrier/Source.lean", "import Mathlib\n"),
            ("tools/lean-inspector-interface/LeanInformationAuditInterface/Syntax.lean", "import Lean\n"));
        AssertNoBlock(Evaluate(Files(), head));
    }

    [Fact]
    public void ImportCommentsCannotGrantDebt()
    {
        AssertBlock(Evaluate(Files((Source, $"/- import {Judge} -/\n")),
            Files((Source, $"import {Judge}\n"))), Source, Judge);
    }

    [Fact]
    public void MalformedPackageDeclarationFailsClosed()
    {
        var head = Files();
        head[Lakefile] = "not valid TOML";
        AssertBlock(Evaluate(Files(), head), Lakefile, "REG-IMPLEMENTATION");
    }

    [Fact]
    public void ImplementationOwnershipCannotHideBehindModuleName()
    {
        var head = Files((Source, "import RenamedJudge\n"),
            ("tools/lean-inspector/RenamedJudge.lean", "import Lean\n"));
        AssertBlock(Evaluate(Files(), head), Source, "RenamedJudge");
    }

    [Fact]
    public void DeletingDebtOwnerPasses()
    {
        AssertNoBlock(Evaluate(Files((Source, $"import {Judge}\n")), Files()));
    }

    [Fact]
    public void IndirectCyclesTerminateAndStillFindImplementation()
    {
        var head = Files((Source, "import Reg.Helper\n"),
            ("Reg/Helper.lean", $"import Reg.Source\nimport {Judge}\n"));
        AssertBlock(Evaluate(Files(), head), "Reg/Helper.lean", Judge);
    }

    [Fact]
    public void ChangedPackageConfigMustReduceItsDebt()
    {
        var baseline = Files();
        baseline[Lakefile] += "\n[[require]]\nname = \"leanInspector\"\npath = \"../tools/lean-inspector\"\n";
        var head = new Dictionary<string, string>(baseline) { [Lakefile] = baseline[Lakefile] + "# edit\n" };
        AssertBlock(Evaluate(baseline, head), Lakefile, "strictly reduce");
    }

    [Fact]
    public void DebtMayNotBeReplacedByARequire()
    {
        var baseline = Files((Source, $"import {Judge}\n"));
        var head = Files();
        head[Lakefile] += "\n[[require]]\nname = \"leanInspector\"\npath = \"../tools/lean-inspector\"\n";
        AssertBlock(Evaluate(baseline, head), Lakefile, "leanInspector");
    }

    [Fact]
    public void MissingInterfaceDependencyFailsClosed()
    {
        AssertBlock(Evaluate(Files(), Files((Source, "import LeanInformationAuditInterface.Missing\n"))),
            Lakefile, "missing package dependency");
    }

    [Theory]
    [InlineData("Reg/Source.lean")]
    [InlineData("Reg/lakefile.toml")]
    [InlineData("Reg.lean")]
    [InlineData("Other/Helper.lean")]
    public void RuleSelectsCompletePackageClosure(string path)
    {
        var rule = RepositoryRules.CreateRegistrations().Single(r => r.Descriptor.Id == RuleId.CreateKnown(1)).Rule;
        Assert.True(rule.IsAffectedBy(Context(Files(), Files(), Reports(), [path])));
    }

    private static Dictionary<string, string> Files(params (string Path, string Text)[] files)
    {
        var result = files.ToDictionary(item => item.Path, item => item.Text, StringComparer.Ordinal);
        result[Lakefile] = Config;
        return result;
    }

    private static ImmutableArray<Diagnostic> Evaluate(Dictionary<string, string> baseline,
        Dictionary<string, string> head, string[]? changedPaths = null) =>
        EvaluateCore(baseline, head, Reports(), changedPaths);

    private static void AssertBlock(IEnumerable<Diagnostic> diagnostics, string path, string message) =>
        Assert.Contains(diagnostics, d => d.AdmissionEffect == AdmissionEffect.Block && d.Path == path
            && d.Message.Contains(message, StringComparison.Ordinal));

    private static void AssertNoBlock(IEnumerable<Diagnostic> diagnostics) =>
        Assert.DoesNotContain(diagnostics, d => d.AdmissionEffect == AdmissionEffect.Block);

    private static LeanAxiomReport Reports(params (string Path, string[] Imports)[] files) =>
        LeanAxiomReport.Create(files.ToDictionary(item => item.Path,
            item => new LeanFileReport(item.Imports.ToImmutableArray(), []), StringComparer.Ordinal));

    private static ImmutableArray<Diagnostic> EvaluateCore(Dictionary<string, string> baseline,
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
        var policy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(TestFileMap.Canonical),
            Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;
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

}
