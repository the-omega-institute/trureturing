using System.Collections.Immutable;
using System.Text;
using StrataLint.Configuration;
using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Rules.Tests;

public sealed class RegistrationSelfAssessmentTests
{
    private const string Registration = "Reg/D5/S0/Carrier/Source.lean";

    [Fact]
    public void NewRunMetaBlocks() => AssertBlocked("open Lean in\nrun_meta do\n  pure ()\n", "run_meta");

    [Fact]
    public void NewTemplateBindingRecordsBlocks() =>
        AssertBlocked("def row := TemplateBinding.records env\n", "TemplateBinding");

    [Fact]
    public void NewEvalBlocks() => AssertBlocked("#eval 1\n", "#eval");

    [Fact]
    public void NewInformationRegistryEntriesBlocks() =>
        AssertBlocked("def rows := LeanInformationAudit.InformationRegistry.entries env\n", "InformationRegistry");

    [Fact]
    public void ByteIdenticalBaselineSelfAssessmentPassesEvenWithChangedPathSignal()
    {
        var files = Files((Registration, "run_meta do\n  pure ()\n"));
        AssertNoBlock(Evaluate(files, new(files), [Registration]));
    }

    [Fact]
    public void ChangedBaselineKeepingSelfAssessmentBlocks()
    {
        const string source = "run_meta do\n  pure ()\n";
        AssertBlocked(Evaluate(Files((Registration, source)),
            Files((Registration, source + "-- edited\n"))), Registration, "run_meta");
    }

    [Fact]
    public void RemovingBaselineSelfAssessmentPasses() => AssertNoBlock(Evaluate(
        Files((Registration, "run_meta do\n  pure ()\n")), Files((Registration, "-- moved downstream\n"))));

    [Fact]
    public void DeletedBaselineSelfAssessmentPasses() =>
        AssertNoBlock(Evaluate(Files((Registration, "run_meta do\n  pure ()\n")), Files()));

    [Fact]
    public void LineCommentsPass() => AssertNoBlock(Evaluate(Files(), Files((Registration,
        "-- run_meta #eval TemplateBinding InformationRegistry\nimport D5.S0.Carrier.Source\n"))));

    [Fact]
    public void NestedBlockCommentsAndDocstringsPass() => AssertNoBlock(Evaluate(Files(), Files((Registration,
        "/- run_meta /- #eval -/ TemplateBinding -/\n"
        + "/-- InformationRegistry /- run_meta -/ -/\n/-! #eval TemplateBinding -/\n"))));

    [Fact]
    public void TokenAfterNestedCommentBlocks() => AssertBlocked(
        "/- outer /- run_meta -/ -- still block\n-/\n#eval 1\n", "#eval");

    [Fact]
    public void CommentsDoNotJoinIdentifierFragments() => AssertNoBlock(Evaluate(Files(), Files((Registration,
        "run_/- gap -/meta Template/- gap -/Binding Information/- gap -/Registry\n"))));

    [Fact]
    public void LongerTemplateBindingPrefixBlocks() => AssertBlocked("#check TemplateBindingX\n", "TemplateBindingX");

    [Fact]
    public void LongerInformationRegistryPrefixBlocks() =>
        AssertBlocked("#check InformationRegistryX\n", "InformationRegistryX");

    [Fact]
    public void LongerUnrelatedIdentifiersPass() => AssertNoBlock(Evaluate(Files(), Files((Registration,
        "def myrun_meta := 1\ndef run_metaX := 2\ndef myTemplateBinding := 3\n"
        + "def myInformationRegistry := 4\ndef run_meta' := 5\n#evaluate 1\n"))));

    [Fact]
    public void D5SourceTokensPass() => AssertNoBlock(Evaluate(Files(), Files(("D5/S0/Carrier/Source.lean",
        "run_meta do\n  pure ()\n#eval TemplateBinding.records InformationRegistry.entries\n"))));

    [Fact]
    public void NonLeanRegFilePasses() => AssertNoBlock(Evaluate(Files(), Files(("Reg/Notes.md",
        "run_meta #eval TemplateBinding InformationRegistry\n"))));

    [Fact]
    public void RegOnlyChangeActivatesDelta()
    {
        var context = Context(Files(), Files((Registration, "run_meta do\n  pure ()\n")));
        Assert.True(DeltaRule().IsAffectedBy(context));
    }

    [Fact]
    public void NonRegDocumentationDoesNotActivateDelta() =>
        Assert.False(DeltaRule().IsAffectedBy(Context(Files(), Files(("docs/Notes.md", "run_meta\n")))));

    [Fact]
    public void RegImportsRemainOutsideD5DirectionCheck() => AssertNoBlock(Evaluate(Files(), Files((Registration,
        "import D5.S0.Carrier.Source\nimport LeanInformationAudit.Syntax\n"))));

    private static void AssertBlocked(string text, string token) =>
        AssertBlocked(Evaluate(Files(), Files((Registration, text))), Registration, token);

    private static void AssertBlocked(IEnumerable<Diagnostic> diagnostics, string path, string token) =>
        Assert.Contains(diagnostics, d => d.RuleId == RuleId.CreateKnown(1) && d.Path == path
            && d.AdmissionEffect == AdmissionEffect.Block
            && d.Message == $"REG-SELF-ASSESSMENT: Reg module may not read or assert registration assessment at compile time ({token}); move the check to LeanInformationAuditRegTests");

    private static void AssertNoBlock(IEnumerable<Diagnostic> diagnostics) =>
        Assert.DoesNotContain(diagnostics, d => d.AdmissionEffect == AdmissionEffect.Block);

    private static Dictionary<string, string> Files(params (string Path, string Text)[] files) =>
        files.ToDictionary(item => item.Path, item => item.Text, StringComparer.Ordinal);

    private static ImmutableArray<Diagnostic> Evaluate(Dictionary<string, string> baseline,
        Dictionary<string, string> head, string[]? changedPaths = null) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(1), Context(baseline, head, changedPaths)).Diagnostics;

    private static IRepositoryRule DeltaRule() =>
        RepositoryRules.CreateRegistrations().Single(r => r.Descriptor.Id == RuleId.CreateKnown(1)).Rule;

    private static DeltaRuleContext Context(Dictionary<string, string> baseline,
        Dictionary<string, string> head, string[]? changedPaths = null)
    {
        var registration = EngineeringRegistrationFixture.Manifest();
        baseline[EngineeringRegistrationFixture.Path] = registration;
        head[EngineeringRegistrationFixture.Path] = registration;
        var changes = RawChangeSet.Create(changedPaths ?? baseline.Keys.Union(head.Keys)
            .Where(path => baseline.GetValueOrDefault(path) != head.GetValueOrDefault(path)));
        var policy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(TestFileMap.Canonical), Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;
        var meta = BootstrapGate.Evaluate(changes) switch
        {
            BootstrapOutcome.Clear clear => MetaEvaluationProfile.ForClear(clear.Capability),
            BootstrapOutcome.ProtectedSurfaceVerificationRequired required =>
                MetaEvaluationProfile.ForProtectedSurface(required.ChangeSet),
            _ => throw new InvalidOperationException("invalid synthetic bootstrap"),
        };
        // Reg need not be present in the Lean report: enforcement reads snapshot bytes.
        return DeltaRuleContext.Create(Tree(head), Tree(baseline), policy,
            AcceptedLeanClosure.Create(LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>())), changes, meta);
    }

    private static RepositorySnapshot Tree(Dictionary<string, string> files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            files.Select(item => RawRepositoryEntry.FromText(item.Key, item.Value))))).Snapshot;
}
