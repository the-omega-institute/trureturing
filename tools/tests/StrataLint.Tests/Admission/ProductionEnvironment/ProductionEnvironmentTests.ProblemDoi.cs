using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private const string ProblemDoiPath = "Problems/sample-open-problem.md";

    [Fact]
    public void CheckRejectsAddedLegacyProblemDossier() => AssertProblemMigrationRejected(
        null, MigrationDossier("arxiv_id: 2305.08349"));

    [Fact]
    public void CheckRejectsEditedLegacyProblemDossier() => AssertProblemMigrationRejected(
        MigrationDossier("arxiv_id: 2305.08349"),
        MigrationDossier("arxiv_id: 2305.08349") + "\nChanged prose.\n");

    [Fact]
    public void CheckRejectsDoiProblemDowngradeToLegacy() => AssertProblemMigrationRejected(
        MigrationDossier("doi: 10.48550/arXiv.2305.08349"),
        MigrationDossier("arxiv_id: 2305.08349"));

    [Fact]
    public void CheckRejectsRenamedLegacyProblemDossier()
    {
        var fixture = TrustedFrozenFixture();
        fixture.Baseline["Problems/old-problem.md"] = MigrationDossier("arxiv_id: 2305.08349")
            .Replace("sample-open-problem", "old-problem", StringComparison.Ordinal);
        fixture.Files[ProblemDoiPath] = MigrationDossier("arxiv_id: 2305.08349");
        AssertProblemMigrationRejected(CheckProblemMigration(fixture,
            RawChangeSet.CreateWithKinds([
                ("Problems/old-problem.md", RawChangeKind.Deleted),
                (ProblemDoiPath, RawChangeKind.Added),
            ])));
    }

    [Fact]
    public void CheckRejectsLegacyProblemEvenWhenChangeListOmitsIt()
    {
        var fixture = TrustedFrozenFixture();
        fixture.Files[ProblemDoiPath] = MigrationDossier("arxiv_id: 2305.08349");
        AssertProblemMigrationRejected(CheckProblemMigration(fixture, RawChangeSet.Create([])));
    }

    [Fact]
    public void CheckAcceptsUnchangedLegacyProblemOnUnrelatedDelta()
    {
        var fixture = TrustedFrozenFixture();
        fixture.Files[ProblemDoiPath] = MigrationDossier("arxiv_id: 2305.08349");
        fixture.Baseline[ProblemDoiPath] = fixture.Files[ProblemDoiPath];
        fixture.Files[RuleFixture.BlueprintPath] += "\nUnrelated prose.\n";
        Assert.IsType<AdmissionOutcome.Admitted>(CheckProblemMigration(fixture,
            RawChangeSet.Create([RuleFixture.BlueprintPath])));
    }

    [Fact]
    public void CheckAcceptsByteIdenticalLegacyProblemDespiteChangedPathHint()
    {
        var fixture = TrustedFrozenFixture();
        fixture.Files[ProblemDoiPath] = MigrationDossier("arxiv_id: 2305.08349");
        fixture.Baseline[ProblemDoiPath] = fixture.Files[ProblemDoiPath];
        Assert.IsType<AdmissionOutcome.Admitted>(CheckProblemMigration(fixture,
            RawChangeSet.Create([ProblemDoiPath])));
    }

    [Fact]
    public void CheckAcceptsDoiMigrationOfLegacyProblem() => AssertProblemMigrationAccepted(
        MigrationDossier("arxiv_id: 2305.08349"), MigrationDossier("doi: 10.48550/arXiv.2305.08349"));

    [Fact]
    public void CheckAcceptsAddedJournalDoiProblem() => AssertProblemMigrationAccepted(
        null, MigrationDossier("doi: 10.1006/eujc.1998.0211"));

    [Fact]
    public void CheckAcceptsDeletedLegacyProblem()
    {
        var fixture = TrustedFrozenFixture();
        fixture.Baseline[ProblemDoiPath] = MigrationDossier("arxiv_id: 2305.08349");
        Assert.IsType<AdmissionOutcome.Admitted>(CheckProblemMigration(fixture,
            RawChangeSet.CreateWithKinds([(ProblemDoiPath, RawChangeKind.Deleted)])));
    }

    private static void AssertProblemMigrationRejected(string? baseline, string current) =>
        AssertProblemMigrationRejected(CheckProblemMigration(MigrationFixture(baseline, current),
            RawChangeSet.Create([ProblemDoiPath])));

    private static void AssertProblemMigrationRejected(AdmissionOutcome outcome)
    {
        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("problem-doi-required", failure.Message, StringComparison.Ordinal);
        Assert.Contains(ProblemDoiPath, failure.Message, StringComparison.Ordinal);
    }

    private static void AssertProblemMigrationAccepted(string? baseline, string current) =>
        Assert.IsType<AdmissionOutcome.Admitted>(CheckProblemMigration(MigrationFixture(baseline, current),
            RawChangeSet.Create([ProblemDoiPath])));

    private static RuleFixture MigrationFixture(string? baseline, string current)
    {
        var fixture = TrustedFrozenFixture();
        fixture.Files[ProblemDoiPath] = current;
        if (baseline is not null) fixture.Baseline[ProblemDoiPath] = baseline;
        return fixture;
    }

    private static AdmissionOutcome CheckProblemMigration(RuleFixture fixture, RawChangeSet changes) =>
        CheckWithReports(new ProductionCliEnvironment("/repo",
            new FakeRepositoryGateway(changes, Snapshot(fixture.Files), Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null)), fixture);

    private static string MigrationDossier(string source) => $$"""
        ---
        slug: sample-open-problem
        bibkey: sos1957threegap
        {{source}}
        triage: theorem
        motivation_gids:
          - D5/S0/Carrier/Ring
        ---

        ## Problem
        Prove the external statement.
        ## Motivation
        A frozen carrier supplies the setting.
        ## Gap
        The statement is unresolved here.
        ## Route
        Prove a bound.
        ## Falsifier
        An exact counterexample.
        ## Evidence
        A finite probe.
        ## Triage
        theorem
        ## ASSUMED-UNVERIFIED
        Later literature has not been checked.
        """ + "\n";
}
