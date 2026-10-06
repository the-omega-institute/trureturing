using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void AlignMovesAnEntryToItsDerivedStatusAndPlanDoesNotWrite()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var recorded = fixture.Files[RuleFixture.FixtureBackfillAtomPath];
        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        var driftedPath =
            $"{BackfillInventoryLoader.RootPath}fixture-source/absorbed-closed/{RuleFixture.FixtureAtomId}.yaml";
        fixture.Files[driftedPath] = recorded;
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var environment = AlignEnvironment(temporary.Path, fixture);

        var plan = environment.AlignDigestionStatus(["--plan"]);

        Assert.True(plan.Success, plan.Error);
        Assert.StartsWith("ALIGN entries=1 status_changed=1 ", plan.Output, StringComparison.Ordinal);
        Assert.Contains("applied=false\n", plan.Output, StringComparison.Ordinal);
        Assert.Contains(
            $"ALIGN_ENTRY source=fixture-source atom={RuleFixture.FixtureAtomId} from=absorbed-closed to=",
            plan.Output,
            StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));

        var applied = environment.AlignDigestionStatus([]);

        Assert.True(applied.Success, applied.Error);
        Assert.Equal(
            plan.Output.Replace("applied=false", "applied=true", StringComparison.Ordinal),
            applied.Output);
        Assert.False(File.Exists(Path.Combine(temporary.Path, driftedPath)));
        var entry = Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries());
        Assert.NotEqual(
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            entry.ProjectedStatus);
    }

    [Fact]
    public void AlignLeavesAnAlignedLedgerUntouched()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var first = AlignEnvironment(temporary.Path, fixture).AlignDigestionStatus([]);
        Assert.True(first.Success, first.Error);
        var settled = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var current = new RuleFixture();
        current.AddBackfillTargets();
        foreach (var path in current.Files.Keys.Where(BackfillInventoryLoader.IsCanonicalPath).ToArray())
        {
            current.Files.Remove(path);
        }

        foreach (var file in Directory.EnumerateFiles(
                     Path.Combine(temporary.Path, "Meta", "Digestion", "backfill"), "*", SearchOption.AllDirectories))
        {
            current.Files[Path.GetRelativePath(temporary.Path, file).Replace(Path.DirectorySeparatorChar, '/')] =
                File.ReadAllText(file);
        }

        var second = AlignEnvironment(temporary.Path, current).AlignDigestionStatus([]);

        Assert.True(second.Success, second.Error);
        Assert.Equal(
            "ALIGN entries=1 status_changed=0 coverage_retargeted=0 ledger_files_changed=0 applied=true\n",
            second.Output);
        Assert.Equal(settled, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Theory]
    [InlineData("--base|baseline")]
    [InlineData("--plan|--plan")]
    [InlineData("extra")]
    [InlineData("--plan|extra")]
    public void AlignRejectsMalformedArgumentsWithoutReadingInputs(string input)
    {
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(new RuleFixture().Files), null);
        var reports = new FakeLeanReportSource(null);
        var environment = new ProductionCliEnvironment(
            "/repo", repository, reports, new FakeScribeEmissionVerifier(null));

        var result = environment.AlignDigestionStatus(input.Split('|'));

        Assert.False(result.Success);
        Assert.StartsWith("ALIGN_INVALID USAGE:", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, repository.WholeTreeReadCount);
        Assert.Empty(repository.ScopedCurrentReads);
        Assert.Equal(0, reports.CallCount);
    }

    [Fact]
    public void AlignFailsWithoutWritingWhenTheLeanReportIsUnavailable()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), null),
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(null));

        var result = environment.AlignDigestionStatus([]);

        Assert.False(result.Success);
        Assert.StartsWith("ALIGN_INVALID ", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    private static ProductionCliEnvironment AlignEnvironment(string root, RuleFixture fixture) =>
        new(root,
            new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(null));
}
