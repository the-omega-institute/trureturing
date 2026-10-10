using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.CoverBatch.Tests;

public sealed partial class CoverBatchCommandTests
{
    private const string ExternalGid = "D5/S0/Carrier/Zeta.zeta";
    private const string ExternalPath = "D5/S0/Carrier/Zeta.lean";

    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, true, false)]
    [InlineData(false, false, true)]
    [InlineData(false, true, true)]
    [InlineData(true, false, false)]
    [InlineData(true, true, false)]
    [InlineData(true, false, true)]
    [InlineData(true, true, true)]
    public void ExistingAndChainCoverageIdentityDriftIsCheckedBeforeBatchWrite(
        bool chain, bool changeIdentity, bool fullReport)
    {
        using var world = new BatchWorld(chain: chain, externalChild: chain, secondaryTarget: true);
        var atom = chain ? world.ParentId! : First;
        var initial = chain ? Row(world.ChildIds[0], Gid) + Row(world.ChildIds[1], ExternalGid)
            : Row(atom, ExternalGid);
        var initialized = world.Run(initial);
        Assert.True(initialized.Success, initialized.Error + initialized.Output);
        var before = world.LedgerImage();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(world.Repository.ReadCurrent())).Snapshot;
        var reports = world.Report.Load(snapshot).Files.ToDictionary(pair => pair.Key.Value, pair => pair.Value);
        if (changeIdentity)
        {
            File.AppendAllText(Path.Combine(world.Root, ExternalPath), "\ntheorem zeta : True ∧ True := ⟨True.intro, True.intro⟩\n");
            reports[ExternalPath] = reports[ExternalPath] with
            {
                Declarations = reports[ExternalPath].Declarations.Select(declaration => declaration with
                {
                    TypeRepresentation = "True ∧ True", PrecomputedStatementId = null,
                }).ToImmutableArray(),
            };
        }
        var report = LeanAxiomReport.Create(reports);

        var result = world.Run(Row(atom, OtherGid), fullReport ? new FullCurrentReport(report) : new FakeLeanReportSource(report));

        Assert.True(result.Success == !changeIdentity, result.Error + result.Output);
        if (changeIdentity)
        {
            Assert.Contains("coverage-target-mismatch", result.Output, StringComparison.Ordinal);
            Assert.Equal(before, world.LedgerImage());
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CoverInputSelectionIncludesExistingAndChainTargetsWithoutLoadingReport(bool batch)
    {
        using var world = new BatchWorld(chain: true, externalChild: true, secondaryTarget: true);
        Assert.True(world.Run(Row(world.ChildIds[0], Gid) + Row(world.ChildIds[1], ExternalGid)).Success);
        var before = world.LedgerImage();
        var noReport = new FakeLeanReportSource(null);

        var result = batch
            ? world.Run(Row(world.ParentId!, OtherGid), noReport, leanInputs: true)
            : CoverAtomCommand.Run(world.Root, world.Repository, noReport, CoverWorld.FixtureUtc,
                ["--lean-inputs", "--cover-atom", world.ParentId!, "--gid", OtherGid]);

        Assert.True(result.Success, result.Error + result.Output);
        Assert.Equal("D5.S0.Carrier.Probe D5.S0.Carrier.Zeta\n", result.Output);
        Assert.Equal(0, noReport.CallCount);
        Assert.Equal(before, world.LedgerImage());
    }

    private sealed class FullCurrentReport(LeanAxiomReport report) : ILeanReportSource
    {
        public LeanAxiomReport Load(RepositorySnapshot snapshot) => report;
        public LeanAxiomReport Load(LeanReportScope scope) => report;
    }
}
