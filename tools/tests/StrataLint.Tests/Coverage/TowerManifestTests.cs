using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TowerManifestTests
{
    [Fact]
    public void EngineeringMembersComeFromChecksAndExcludeNullAndDirectChecks()
    {
        var syntax = RegisteredSyntax();
        var snapshot = Snapshot(
            ("Meta/ci-units.json", Registration),
            (".github/workflows/ci-fixture.yml", UnitWorkflow),
            (".github/workflows/ci-current.yml", "opaque direct workflow"),
            (".github/workflows/ci-skipped.yml", "opaque optional workflow"),
            (".github/workflows/ci-unit.yml", "opaque reusable workflow"),
            LedgerAnchorFile());

        var accepted = Assert.IsType<TowerValidationOutcome.Accepted>(
            TowerManifestValidator.Validate(syntax, snapshot, Catalog()));
        var check = Assert.Single(accepted.Manifest.Checks.Where(item => item.Subject == "engineering-ci"));
        Assert.Contains("fixture workflow=.github/workflows/ci-fixture.yml", check.Detail, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing-job")]
    [InlineData("wrong-workflow")]
    [InlineData("name-only")]
    [InlineData("missing-workflow")]
    [InlineData("unregistered-workflow")]
    [InlineData("malformed-workflow")]
    public void RegisteredMembersAndWorkflowInventoryAreCheckedBothWays(string defect)
    {
        var files = new List<(string Path, string Text)>
        {
            ("Meta/ci-units.json", Registration),
            (".github/workflows/ci-fixture.yml", UnitWorkflow),
            (".github/workflows/ci-current.yml", UnitWorkflow),
            (".github/workflows/ci-skipped.yml", "opaque optional workflow"),
            LedgerAnchorFile(),
        };
        switch (defect)
        {
            case "missing-job": files[1] = (files[1].Path, UnitWorkflow.Replace("fixture:", "other:", StringComparison.Ordinal)); break;
            case "name-only": files[1] = (files[1].Path, UnitWorkflow.Replace("fixture: {", "other: {name: fixture, ", StringComparison.Ordinal)); break;
            case "wrong-workflow": files[0] = (files[0].Path, Registration.Replace("ci-fixture.yml", "ci-wrong.yml", StringComparison.Ordinal)); break;
            case "missing-workflow": files.RemoveAt(1); break;
            case "unregistered-workflow": files.Add((".github/workflows/ci-new.yml", UnitWorkflow)); break;
            case "malformed-workflow": files[1] = (files[1].Path, "jobs: ["); break;
        }

        var rejected = Assert.IsType<TowerValidationOutcome.Rejected>(
            TowerManifestValidator.Validate(RegisteredSyntax(), Snapshot(files.ToArray()), Catalog()));
        Assert.Contains(rejected.Findings, item => item.Component == "engineering-ci"
            && item.Code == (defect == "unregistered-workflow" ? "TOWER-CI-WORKFLOW" : "TOWER-CI-JOB"));
    }

    [Theory]
    [InlineData(null)]
    [InlineData("{")]
    [InlineData("{\"schema\":\"other\",\"units\":[]}")]
    [InlineData("{\"schema\":\"ci-units-v1\",\"units\":{}}")]
    [InlineData("{\"schema\":\"ci-units-v1\",\"units\":[]}")]
    [InlineData("{\"schema\":\"ci-units-v1\",\"units\":[{\"id\":\"fixture\",\"workflow\":\".github/workflows/ci-fixture.yml\"}]}")]
    [InlineData("{\"schema\":\"ci-units-v1\",\"units\":[{\"id\":\"fixture\",\"workflow\":\"../ci-fixture.yml\",\"check\":\"fixture / unit\"}]}")]
    [InlineData("{\"schema\":\"ci-units-v1\",\"units\":[{\"id\":\"fixture\",\"workflow\":\".github/workflows/ci-fixture.yml\",\"check\":false}]}")]
    [InlineData("{\"schema\":\"ci-units-v1\",\"units\":[{\"id\":\"fixture\",\"workflow\":\".github/workflows/ci-fixture.yml\",\"check\":null}]}")]
    public void MissingMalformedOrEmptyMemberRegistrationFailsClosed(string? registration)
    {
        var files = new List<(string Path, string Text)> { LedgerAnchorFile() };
        if (registration is not null) files.Add(("Meta/ci-units.json", registration));
        var rejected = Assert.IsType<TowerValidationOutcome.Rejected>(
            TowerManifestValidator.Validate(RegisteredSyntax(), Snapshot(files.ToArray()), Catalog()));
        Assert.Contains(rejected.Findings, item => item.Code == "TOWER-CI-UNITS");
    }

    [Theory]
    [InlineData("engineering-ci", "members: [fixture]")]
    [InlineData("engineering-ci", "members_from: other")]
    [InlineData("engineering-ci", "members_from: ci-units\n    members: [fixture]")]
    [InlineData("report-ci", "members_from: ci-units")]
    public void MemberSourceIsClosedAndEngineeringCannotHandListMembers(string id, string members)
    {
        var parsed = TowerManifestParser.Parse(Encoding.UTF8.GetBytes(RegisteredYaml(id, members)));
        if (parsed is TowerManifestParseOutcome.Loaded loaded)
            Assert.IsType<TowerValidationOutcome.Rejected>(TowerManifestValidator.ValidateStructure(loaded.Syntax));
        else
            Assert.IsType<TowerManifestParseOutcome.Invalid>(parsed);
    }

    private const string UnitWorkflow = "on: {pull_request: {branches: [dev]}, push: {branches: [dev]}}\njobs: {fixture: {uses: ./unit.yml}}";
    private const string Registration = """
        {"schema":"ci-units-v1","units":[
          {"id":"current","workflow":".github/workflows/ci-current.yml","check":"current"},
          {"id":"fixture","workflow":".github/workflows/ci-fixture.yml","check":"fixture / unit"},
          {"id":"skipped","workflow":".github/workflows/ci-skipped.yml","check":null}]}
        """;

    private static TowerManifestSyntax RegisteredSyntax() =>
        Assert.IsType<TowerManifestParseOutcome.Loaded>(TowerManifestParser.Parse(
            Encoding.UTF8.GetBytes(RegisteredYaml("engineering-ci", "members_from: ci-units")))).Syntax;

    private static string RegisteredYaml(string id, string members) => $$"""
        schema_version: 1
        components:
          - id: {{id}}
            kind: ci-jobs
            {{members}}
            judged_by:
              - bootstrap-pr-1
            verification: verified
        bootstrap:
          id: bootstrap-pr-1
          judge: open
          reason: "Godel boundary"
          genesis_event: sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262
          commit: f3f471846dd81cfcc39ecaa386966fcf0b058464
          pull_request: 1
          verification: ASSUMED-UNVERIFIED
        """;

    [Fact]
    public void ActualCrossChecksRejectCatalogAndCiDrift()
    {
        var syntax = Syntax(
            Component("rules", "rule-catalog", ["SL-002"], "bootstrap-pr-1"),
            Component("baseline", "ci-jobs", ["current"], "bootstrap-pr-1"));
        var snapshot = Snapshot(
            (RuleFixture.WorkflowPath, "jobs:\n  other-job:\n    name: Other\n"),
            LedgerAnchorFile());
        var catalog = Catalog(RuleId.CreateKnown(1));

        var outcome = TowerManifestValidator.Validate(syntax, snapshot, catalog);

        var rejected = Assert.IsType<TowerValidationOutcome.Rejected>(outcome);
        Assert.Contains(rejected.Findings, item => item.Code == "TOWER-RULE-CATALOG");
        Assert.Contains(rejected.Findings, item => item.Code == "TOWER-CI-JOB");
    }

    /// An equal-sized swap is the case counts cannot report: both sides have one member,
    /// so a count-based message renders "declared 1 ... contains 1" and reads as a broken
    /// tool rather than a mismatch. The finding must name the ids that actually differ.
    /// Fails if the message ever goes back to reporting cardinality (#993).
    [Fact]
    public void RuleCatalogMismatchNamesTheDifferingIdsNotJustTheCount()
    {
        var syntax = Syntax(
            Component("rules", "rule-catalog", ["SL-002"], "bootstrap-pr-1"),
            Component("baseline", "ci-jobs", ["current"], "bootstrap-pr-1"));
        var snapshot = Snapshot(
            (RuleFixture.WorkflowPath, "jobs:\n  delta:\n    name: Baseline\n"),
            LedgerAnchorFile());
        var catalog = Catalog(RuleId.CreateKnown(1));

        var outcome = TowerManifestValidator.Validate(syntax, snapshot, catalog);

        var rejected = Assert.IsType<TowerValidationOutcome.Rejected>(outcome);
        var finding = Assert.Single(
            rejected.Findings.Where(item => item.Code == "TOWER-RULE-CATALOG"));

        Assert.Contains("SL-002", finding.Message, StringComparison.Ordinal);
        Assert.Contains("SL-001", finding.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("declared 1 rules but", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ActualCrossChecksReportVerifiedAndAssumedEvidenceSeparately()
    {
        var syntax = Syntax(
            Component("rules", "rule-catalog", ["SL-001"], "bootstrap-pr-1"),
            Component("baseline", "ci-jobs", ["current"], "bootstrap-pr-1"));
        var snapshot = Snapshot(
            (RuleFixture.WorkflowPath, """
                on: {pull_request: {branches: [dev]}, push: {branches: [dev]}}
                jobs: {current: {runs-on: fixture, steps: [{run: 'dotnet judge.dll check-delta'}]}}
                """),
            LedgerAnchorFile());

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
    public void IndependentChecksComeFromEachRegisteredWorkflow()
    {
        var syntax = Syntax(Component("checks", "ci-jobs", ["tests-fixture", "current"], "bootstrap-pr-1"));
        var snapshot = Snapshot(
            (".github/workflows/ci-tests-fixture.yml", "on: {pull_request: {branches: [dev]}, push: {branches: [dev]}}\njobs: {tests-fixture: {uses: ./unit.yml}}"),
            (".github/workflows/ci-current.yml", "on: {pull_request: {branches: [dev]}, push: {branches: [dev]}}\njobs: {current: {runs-on: fixture, steps: [{run: 'dotnet judge.dll check-delta'}]}}"),
            LedgerAnchorFile());
        var accepted = Assert.IsType<TowerValidationOutcome.Accepted>(
            TowerManifestValidator.Validate(syntax, snapshot, Catalog()));
        Assert.Equal(2, accepted.Manifest.Checks.Count(check => check.Subject == "checks"));
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
    public void AComponentThatProtectsNothingIsRejectedRatherThanReportedVerified()
    {
        var syntax = Syntax(new TowerComponentSyntax(
            "hollow",
            "repository-files",
            ImmutableArray<string>.Empty,
            ["bootstrap-pr-1"],
            "verified"));

        var rejected = Assert.IsType<TowerValidationOutcome.Rejected>(
            TowerManifestValidator.ValidateStructure(syntax));
        Assert.Contains(
            rejected.Findings,
            item => item is { Code: "TOWER-MEMBER", Component: "hollow" });

        // Without the structural rejection the actual pass reports
        // "verified: repository files=0" for a component that guards nothing.
        Assert.IsType<TowerValidationOutcome.Rejected>(
            TowerManifestValidator.Validate(syntax, Snapshot(LedgerAnchorFile()), Catalog()));
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
        var registrations = ids.Select(id => new RuleRegistration(
            new RuleDescriptor(
                id,
                "fixture",
                DisplaySeverity.Error,
                "fixture",
                AdmissionEffect.Block,
                RuleLifecycle.Active,
                null),
            new TowerRule())).ToImmutableArray();
        return RuleCatalog.CreateForTesting(registrations);
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files)
    {
        var raw = RawRepositorySnapshot.Create(
            files.Select(static item => RawRepositoryEntry.FromText(item.Path, item.Text)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static (string Path, string Text) LedgerAnchorFile() => (
        FrozenLedgerChangeClassifier.AcceptedRoot
            + "/fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262.json",
        "{\"event_hash\":\"sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262\",\"event_type\":\"Freeze\"}\n");

    private sealed class TowerRule : IRepositoryRule
    {
        public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) => true;

        public ImmutableArray<RuleFinding> EvaluateCurrent(CurrentRuleContext context) => [];
    }
}
