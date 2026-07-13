using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CoverageAnalyzerTests
{
    [Fact]
    public void EnumeratedArtifactWithoutAnyMechanismIsUngoverned()
    {
        var report = Analyze(RuleLifecycle.Active, applies: false);

        var artifact = Assert.Single(report.Artifacts);
        Assert.True(artifact.IsUngoverned);
        Assert.Equal("scratch/note.txt", Assert.Single(report.Ungoverned).Path.Value);
        var row = Assert.Single(report.Matrix, item => item.Class == ArtifactClass.Other);
        Assert.Equal(1, row.Artifacts);
        Assert.Equal(1, row.Ungoverned);
    }

    [Fact]
    public void ApplicableActiveRuleGovernsTheSameArtifact()
    {
        var report = Analyze(RuleLifecycle.Active, applies: true);

        var artifact = Assert.Single(report.Artifacts);
        Assert.False(artifact.IsUngoverned);
        Assert.Equal(new[] { "SL-001" }, artifact.Mechanisms.ActiveRules.Select(static item => item.Value));
        Assert.Empty(report.Ungoverned);
    }

    [Fact]
    public void DeferredRuleIsReportedButDoesNotMasqueradeAsGovernance()
    {
        var report = Analyze(RuleLifecycle.Deferred, applies: true);

        var artifact = Assert.Single(report.Artifacts);
        Assert.True(artifact.IsUngoverned);
        Assert.Empty(artifact.Mechanisms.ActiveRules);
        Assert.Equal(new[] { "SL-001" }, artifact.Mechanisms.DeferredRules.Select(static item => item.Value));
    }

    [Fact]
    public void MechanismsAreDerivedFromPolicyRuleAndLedgerInputs()
    {
        const string path = "Evidence/D5/values.result.json";
        var snapshot = Snapshot((path, "{}\n"));
        var report = CoverageAnalyzer.Analyze(
            snapshot,
            Policy(),
            RuleCatalog.Default,
            CoverageLedgerIndex.Create((path, CoverageLedgerState.Semantic)));

        var artifact = Assert.Single(report.Artifacts);
        Assert.Equal(ArtifactClass.E, artifact.Class);
        Assert.Equal("structured-json", artifact.Mechanisms.ValidationProfile);
        Assert.Equal(CoverageLedgerState.Semantic, artifact.Mechanisms.LedgerState);
        Assert.Contains("path-policy", artifact.Mechanisms.Registrations);
        Assert.Contains("registry:artifact-kinds", artifact.Mechanisms.Registrations);
        Assert.Contains(RuleId.CreateKnown(18), artifact.Mechanisms.ActiveRules);
    }

    private static CoverageReport Analyze(RuleLifecycle lifecycle, bool applies)
    {
        var snapshot = Snapshot(("scratch/note.txt", "note\n"));
        var deferred = lifecycle is RuleLifecycle.Deferred ? CaseId.CreateKnown("D5-T0099") : null;
        var descriptor = new RuleDescriptor(
            RuleId.CreateKnown(1),
            "fixture",
            DisplaySeverity.Error,
            "fixture",
            AdmissionEffect.Block,
            lifecycle,
            deferred);
        var catalog = RuleCatalog.CreateForTesting(
            [descriptor],
            [new PredicateRule(applies)]);
        return CoverageAnalyzer.Analyze(
            snapshot,
            Policy(),
            catalog,
            CoverageLedgerIndex.Empty);
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files)
    {
        var raw = RawRepositorySnapshot.Create(
            files.Select(static item => RawRepositoryEntry.FromText(item.Path, item.Text)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static ValidatedPolicy Policy() => Assert.IsType<RegistryLoadOutcome.Accepted>(
        RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;

    private sealed class PredicateRule(bool applies) : IRepositoryRule
    {
        public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) => applies;

        public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) => [];
    }
}
