using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleApplicabilityTests
{
    [Fact]
    public void CatalogQueriesTheRuleObjectsOwnApplicabilityPredicate()
    {
        var snapshot = Snapshot(("probe.txt", "probe\n"));
        var context = RuleApplicabilityContext.Create(snapshot, Policy());
        var descriptor = Descriptor(1);
        var catalog = RuleCatalog.CreateForTesting(
            [
                new RuleRegistration(
                    descriptor,
                    new PredicateRule(static file => file.Path.Value == "probe.txt")),
            ]);

        var applicable = catalog.ApplicableTo(snapshot.Files.Values.Single(), context);

        Assert.Equal(new[] { descriptor }, applicable);
    }

    [Theory]
    [InlineData(
        RuleFixture.RingPath,
        "SL-001,SL-002,SL-003,SL-004,SL-006,SL-010,SL-011,SL-012,SL-013,SL-015,SL-017,SL-020")]
    [InlineData("Library/queries.yaml", "SL-003,SL-006,SL-015,SL-017,SL-019")]
    [InlineData(
        RuleFixture.AnchorCatalogPath,
        "SL-003,SL-015,SL-017,SL-019,SL-022")]
    [InlineData(RuleFixture.ValuesProjectionPath, "SL-003,SL-006,SL-015,SL-018,SL-019")]
    [InlineData(RuleFixture.TowerManifestPath, "SL-003,SL-015,SL-019,SL-022")]
    [InlineData(
        RuleFixture.GoldenDataSourcePath,
        "SL-003,SL-015")]
    [InlineData(
        "Blueprint/D5/S1/Digit/LatexFixture.scribe.cs",
        "SL-003,SL-006,SL-011,SL-015,SL-022,SL-023")]
    [InlineData(
        "Golden/cases/CapacityExtra00.toml",
        "SL-003,SL-015")]
    public void DefaultCatalogApplicabilityMatchesTheRulesActualScanSurface(
        string path,
        string expected)
    {
        var text = path.EndsWith(".lean", StringComparison.Ordinal)
            ? Header("D5/S0/Carrier/Ring", "G")
            : "schema_version: 1\n";
        var snapshot = Snapshot((path, text));
        var context = RuleApplicabilityContext.Create(snapshot, Policy());

        var applicable = RuleCatalog.Default.ApplicableTo(snapshot.Files.Values.Single(), context);

        Assert.Equal(expected, string.Join(',', applicable.Select(static item => item.Id.Value)));
    }

    private static RuleDescriptor Descriptor(int number) => new(
        RuleId.CreateKnown(number),
        "fixture",
        DisplaySeverity.Error,
        "fixture",
        AdmissionEffect.Block,
        RuleLifecycle.Active,
        null);

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

    private static string Header(string gid, string generality) => $"""
        /- GID: {gid}
           generality: {generality}
           mirror-B: none(waiver:test)
           mirror-E: none(waiver:test)
           anchors: []
           digest: fixture. -/
        """;

    private sealed class PredicateRule(Func<RepositoryFile, bool> predicate) : IRepositoryRule
    {
        public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) =>
            predicate(artifact);

        public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) =>
            ImmutableArray<RuleFinding>.Empty;
    }
}
