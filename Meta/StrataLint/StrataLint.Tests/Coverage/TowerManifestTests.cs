using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TowerManifestTests
{
    [Fact]
    public void ActualCrossChecksRejectCatalogAndCiDrift()
    {
        var syntax = Syntax(
            Component("rules", "rule-catalog", ["SL-002"], "bootstrap-pr-1"),
            Component("baseline", "ci-jobs", ["baseline-admission"], "bootstrap-pr-1"));
        var snapshot = Snapshot(
            (".github/workflows/ci.yml", "jobs:\n  other-job:\n    name: Other\n"),
            GenesisFile());
        var catalog = Catalog(RuleId.CreateKnown(1));

        var outcome = TowerManifestValidator.Validate(syntax, snapshot, catalog);

        var rejected = Assert.IsType<TowerValidationOutcome.Rejected>(outcome);
        Assert.Contains(rejected.Findings, item => item.Code == "TOWER-RULE-CATALOG");
        Assert.Contains(rejected.Findings, item => item.Code == "TOWER-CI-JOB");
    }

    [Fact]
    public void ActualCrossChecksReportVerifiedAndAssumedEvidenceSeparately()
    {
        var syntax = Syntax(
            Component("rules", "rule-catalog", ["SL-001"], "bootstrap-pr-1"),
            Component("baseline", "ci-jobs", ["baseline-admission"], "bootstrap-pr-1"));
        var snapshot = Snapshot(
            (".github/workflows/ci.yml", """
                jobs:
                  baseline-admission:
                    name: Content-addressed dev baseline admission
                """),
            GenesisFile());

        var accepted = Assert.IsType<TowerValidationOutcome.Accepted>(
            TowerManifestValidator.Validate(syntax, snapshot, Catalog(RuleId.CreateKnown(1))));

        Assert.Contains(accepted.Manifest.Checks, item => item is { Subject: "rules", Status: "verified" });
        Assert.Contains(accepted.Manifest.Checks, item => item is { Subject: "baseline", Status: "verified" });
        Assert.Contains(accepted.Manifest.Checks, item => item is { Subject: "bootstrap-pr-1", Status: "verified" });
        Assert.Contains(
            accepted.Manifest.Checks,
            item => item is { Subject: "bootstrap-pr-1", Status: "ASSUMED-UNVERIFIED" });
    }

    [Fact]
    public void YamlDeclaresMembersAndEdgesWithoutEmbeddingValidationSemantics()
    {
        const string yaml = """
            schema_version: 1
            components:
              - id: sl-rules
                kind: rule-catalog
                members:
                  - SL-001
                  - SL-002
                judged_by:
                  - bootstrap-pr-1
                verification: verified
            bootstrap:
              id: bootstrap-pr-1
              judge: open
              reason: "Godel boundary: the trust root cannot prove its own consistency."
              genesis_event: sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262
              commit: f3f471846dd81cfcc39ecaa386966fcf0b058464
              pull_request: 1
              verification: ASSUMED-UNVERIFIED
            """;

        var parsed = Assert.IsType<TowerManifestParseOutcome.Loaded>(
            TowerManifestParser.Parse(Encoding.UTF8.GetBytes(yaml)));

        var component = Assert.Single(parsed.Syntax.Components);
        Assert.Equal(new[] { "SL-001", "SL-002" }, component.Members);
        Assert.Equal(new[] { "bootstrap-pr-1" }, component.JudgedBy);
        Assert.IsType<TowerValidationOutcome.Accepted>(
            TowerManifestValidator.ValidateStructure(parsed.Syntax));
    }

    [Fact]
    public void CycleIsRejectedWithACanonicalWitness()
    {
        var outcome = Validate(
            Component("a", "b"),
            Component("b", "a"));

        var rejected = Assert.IsType<TowerValidationOutcome.Rejected>(outcome);
        var finding = Assert.Single(rejected.Findings, item => item.Code == "TOWER-CYCLE");
        Assert.Equal("a -> b -> a", finding.Message);
    }

    [Fact]
    public void EveryComponentMustDeclareAtLeastOneJudge()
    {
        var outcome = Validate(new TowerComponentSyntax(
            "orphan",
            "test",
            ImmutableArray<string>.Empty,
            ImmutableArray<string>.Empty,
            "verified"));

        var rejected = Assert.IsType<TowerValidationOutcome.Rejected>(outcome);
        Assert.Contains(
            rejected.Findings,
            item => item is { Code: "TOWER-UNJUDGED", Component: "orphan" });
    }

    [Fact]
    public void BootstrapTopMustBeExplicitlyOpen()
    {
        var syntax = Syntax(Component("leaf", "bootstrap-pr-1")) with
        {
            Bootstrap = Bootstrap() with { Judge = "closed" },
        };

        var outcome = TowerManifestValidator.ValidateStructure(syntax);

        var rejected = Assert.IsType<TowerValidationOutcome.Rejected>(outcome);
        Assert.Contains(rejected.Findings, item => item.Code == "TOWER-TOP-OPEN");
    }

    [Fact]
    public void PhasedGateRecordsImplementedPhaseOneWithoutClaimingFullVerification()
    {
        var syntax = Syntax(new TowerComponentSyntax(
            "conservative-extension-gate-c",
            "phased-gate",
            [
                "phase1-protected-content-admission",
                "phase2-conservative-extension-proof-pending",
            ],
            ["bootstrap-pr-1"],
            "ASSUMED-UNVERIFIED"));

        var accepted = Assert.IsType<TowerValidationOutcome.Accepted>(
            TowerManifestValidator.Validate(syntax, Snapshot(GenesisFile()), Catalog()));

        Assert.Contains(
            accepted.Manifest.Checks,
            static item => item is
            {
                Subject: "conservative-extension-gate-c",
                Status: "ASSUMED-UNVERIFIED",
            });
    }

    private static TowerValidationOutcome Validate(params TowerComponentSyntax[] components) =>
        TowerManifestValidator.ValidateStructure(Syntax(components));

    private static TowerManifestSyntax Syntax(params TowerComponentSyntax[] components) => new(
        1,
        components.ToImmutableArray(),
        Bootstrap());

    private static TowerComponentSyntax Component(string id, params string[] judgedBy) => new(
        id,
        "test",
        ImmutableArray<string>.Empty,
        judgedBy.ToImmutableArray(),
        "verified");

    private static TowerComponentSyntax Component(
        string id,
        string kind,
        string[] members,
        params string[] judgedBy) => new(
        id,
        kind,
        members.ToImmutableArray(),
        judgedBy.ToImmutableArray(),
        "verified");

    private static TowerBootstrapSyntax Bootstrap() => new(
        "bootstrap-pr-1",
        "open",
        "Godel boundary: the trust root cannot prove its own consistency.",
        "sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262",
        "f3f471846dd81cfcc39ecaa386966fcf0b058464",
        1,
        "ASSUMED-UNVERIFIED");

    private static RuleCatalog Catalog(params RuleId[] ids)
    {
        var descriptors = ids.Select(id => new RuleDescriptor(
            id,
            "fixture",
            DisplaySeverity.Error,
            "fixture",
            AdmissionEffect.Block,
            RuleLifecycle.Active,
            null)).ToImmutableArray();
        var rules = ids.Select(static _ => (IRepositoryRule)new TowerRule()).ToImmutableArray();
        return RuleCatalog.CreateForTesting(descriptors, rules);
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files)
    {
        var raw = RawRepositorySnapshot.Create(
            files.Select(static item => RawRepositoryEntry.FromText(item.Path, item.Text)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static (string Path, string Text) GenesisFile() => (
        "Meta/StrataLint/Golden/Frozen/events.jsonl",
        "{\"event_hash\":\"sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262\",\"event_type\":\"Genesis\"}\n");

    private sealed class TowerRule : IRepositoryRule
    {
        public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) => true;

        public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) => [];
    }
}
