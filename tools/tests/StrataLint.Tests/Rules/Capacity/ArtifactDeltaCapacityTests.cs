using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed class ArtifactDeltaCapacityTests
{
    private static readonly RuleId CapacityRule = RuleId.CreateKnown(3);
    private const string Artifact = "CLAUDE.md";

    [Theory]
    [InlineData(RawChangeKind.Added, 0, false)]
    [InlineData(RawChangeKind.Added, 1000, false)]
    [InlineData(RawChangeKind.Added, 1001, true)]
    [InlineData(RawChangeKind.Modified, 0, false)]
    [InlineData(RawChangeKind.Modified, 1000, false)]
    [InlineData(RawChangeKind.Modified, 1001, true)]
    public void ChangedArtifactIsBoundedWithoutCurrentMaterialRegistration(
        RawChangeKind kind, int lines, bool rejected)
    {
        var fixture = Fixture();
        if (kind == RawChangeKind.Modified)
            fixture.Baseline[Artifact] = Lines(1200);
        fixture.Files[Artifact] = Lines(lines);
        var context = fixture.Build(RawChangeSet.CreateWithKinds([(Artifact, kind)]));

        Assert.Empty(RuleCatalog.Default.EvaluateCurrentSingle(CapacityRule, context.CurrentFacts).Diagnostics);
        var diagnostics = RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, context).Diagnostics;
        if (!rejected)
        {
            Assert.Empty(diagnostics);
            return;
        }

        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(Artifact, diagnostic.Path);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("1001 lines (hard limit 1000)", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("tools/StrataLint.Engine/Fixture.cs")]
    [InlineData("Blueprint/D5/S0/Carrier/Fixture.scribe.cs")]
    [InlineData("Problems/oeis-a000001-fixture.md")]
    [InlineData("agents/fixture.md")]
    public void NonRegisteredSourceKindsActivateTheDeltaGate(string path)
    {
        var fixture = Fixture();
        fixture.Files[path] = Lines(1001);
        var context = fixture.Build(RawChangeSet.CreateWithKinds([(path, RawChangeKind.Added)]));

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.ExecuteDelta(context));

        Assert.Contains(CapacityRule, completed.Capability.ExecutedRules);
        Assert.Contains(completed.Capability.Diagnostics, diagnostic => diagnostic.RuleId == CapacityRule
            && diagnostic.Path == path && diagnostic.AdmissionEffect == AdmissionEffect.Block);
    }

    [Theory]
    [InlineData(1000, false)]
    [InlineData(1001, true)]
    public void SourcePrerequisiteUsesTheSameDeltaGate(int lines, bool rejected)
    {
        var fixture = Fixture();
        fixture.Files[Artifact] = Lines(lines);
        var context = fixture.Build(RawChangeSet.CreateWithKinds([(Artifact, RawChangeKind.Added)]));

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.ExecuteSourcePrerequisite(
            context.Current, context.Policy, context.Baseline, context.Changes));

        Assert.Equal(rejected, completed.Capability.Diagnostics.Any(diagnostic => diagnostic.RuleId == CapacityRule
            && diagnostic.Path == Artifact && diagnostic.AdmissionEffect == AdmissionEffect.Block));
    }

    [Theory]
    [InlineData("\n", false)]
    [InlineData("\n", true)]
    [InlineData("\r\n", false)]
    [InlineData("\r\n", true)]
    public void BlankLinesAndTrailingTerminatorsMatchAuditCounting(string newline, bool trailingTerminator)
    {
        foreach (var count in new[] { 1000, 1001 })
        {
            var text = string.Join(newline, Enumerable.Repeat(string.Empty, count - 1).Append("容量"))
                + (trailingTerminator ? newline : string.Empty);
            var snapshot = Snapshot(Artifact, text);

            var findings = RepositoryRules.Capacity(snapshot, Snapshot(),
                RawChangeSet.CreateWithKinds([(Artifact, RawChangeKind.Added)]));

            Assert.Equal(count > 1000, findings.Any());
            Assert.Equal(RepositoryCapacityAudit.InspectFiles([(Artifact, text)]).Select(item => item.Message),
                findings.Select(item => item.Message));
        }
    }

    [Theory]
    [InlineData("data.json")]
    [InlineData("data.JSONL")]
    [InlineData("data.ndjson")]
    [InlineData("data.json5")]
    [InlineData("data.jsonc")]
    [InlineData("data.yaml")]
    [InlineData("data.yml")]
    [InlineData("data.toml")]
    [InlineData("data.csv")]
    [InlineData("data.tsv")]
    [InlineData("data.xml")]
    [InlineData("data.trx")]
    [InlineData("data.b64")]
    [InlineData("docs/develop/spec/fixture.md")]
    [InlineData("docs/develop/theory/Fixture.md")]
    [InlineData("Blueprint/D5/S0/Carrier/Fixture.md")]
    [InlineData("Library/notes/fixture.MD")]
    [InlineData("Meta/BACKFILL.yaml")]
    [InlineData("lake-manifest.json")]
    public void AuditExemptionsAlsoApplyToChangedArtifacts(string path)
    {
        var text = Lines(1001);
        Assert.Empty(RepositoryCapacityAudit.InspectFiles([(path, text)]));

        Assert.Empty(RepositoryRules.Capacity(Snapshot(path, text), Snapshot(),
            RawChangeSet.CreateWithKinds([(path, RawChangeKind.Added)])));
    }

    [Theory]
    [InlineData("agents/other.md")]
    [InlineData("tools/StrataLint.Engine/Rules/FutureRule.cs")]
    public void UntouchedOversizeArtifactsRemainOutsideDeltaScope(string changedPath)
    {
        var fixture = Fixture();
        fixture.Files[Artifact] = fixture.Baseline[Artifact] = Lines(1200);
        fixture.Files[changedPath] = "changed\n";
        var context = fixture.Build(RawChangeSet.CreateWithKinds([(changedPath, RawChangeKind.Added)]));

        Assert.Empty(RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, context).Diagnostics);
    }

    [Fact]
    public void DeletedArtifactDoesNotMaterializeEitherBody()
    {
        var path = RepoPath.CreateKnown(Artifact);
        var poison = new RepositoryFile(path, ImmutableArray.Create((byte)0xff), false, null);
        Assert.Throws<DecoderFallbackException>(() => poison.Text);
        var snapshot = RepositorySnapshot.Create(ImmutableDictionary<RepoPath, RepositoryFile>.Empty.Add(path, poison));

        Assert.Empty(RepositoryRules.Capacity(snapshot, snapshot,
            RawChangeSet.CreateWithKinds([(Artifact, RawChangeKind.Deleted)])));
        Assert.Empty(RepositoryRules.Capacity(Snapshot(), snapshot,
            RawChangeSet.CreateWithKinds([(Artifact, RawChangeKind.Deleted)])));
    }

    [Theory]
    [InlineData(RawChangeKind.Deleted)]
    [InlineData(RawChangeKind.Copied)]
    public void RenameAndCopyDestinationsAreNewArtifacts(RawChangeKind sourceKind)
    {
        const string source = "docs/develop/old.md";
        var fixture = Fixture();
        fixture.Baseline[source] = Lines(1001);
        if (sourceKind == RawChangeKind.Copied)
            fixture.Files[source] = fixture.Baseline[source];
        fixture.Files[Artifact] = fixture.Baseline[source];
        var context = fixture.Build(RawChangeSet.CreateWithKinds(
            [(source, sourceKind), (Artifact, RawChangeKind.Added)]));

        var diagnostic = Assert.Single(RuleCatalog.Default.EvaluateDeltaSingle(CapacityRule, context).Diagnostics);
        Assert.Equal(Artifact, diagnostic.Path);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    private static RuleFixture Fixture()
    {
        var fixture = new RuleFixture();
        fixture.Files["Meta/ci-checks.json"] = fixture.Baseline["Meta/ci-checks.json"] = """
            {"schema":"ci-check-input-registration-v2","checks":[
              {"id":"SL-003","materials":["D5/**"],"material_excludes":[]},
              {"id":"SL-015","materials":["**/*.json"],"material_excludes":[]}
            ]}
            """ + "\n";
        return fixture;
    }

    private static RepositorySnapshot Snapshot(string? path = null, string text = "") =>
        RepositorySnapshot.Create(path is null ? ImmutableDictionary<RepoPath, RepositoryFile>.Empty
            : ImmutableDictionary<RepoPath, RepositoryFile>.Empty.Add(RepoPath.CreateKnown(path),
                new RepositoryFile(RepoPath.CreateKnown(path), [], text)));

    private static string Lines(int count) => string.Concat(Enumerable.Repeat("line\n", count));
}
