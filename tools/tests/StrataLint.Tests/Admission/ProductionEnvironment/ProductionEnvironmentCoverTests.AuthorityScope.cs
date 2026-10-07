using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CoverAtomIgnoresUnreferencedInvalidCoverageOutsideFrozenClosure()
    {
        const string siblingModuleGid = "D5/S0/Carrier/CoverSibling";
        const string siblingGid = siblingModuleGid + ".sibling";
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            SecondaryTarget = (siblingModuleGid, "sibling"),
            UnrelatedSibling = new CoverUnrelatedSiblingSpec(
                [siblingGid],
                [siblingGid],
                []),
        });
        var inputs = DirectoryInputs(WithInvalidSiblingCoverage(materialized));
        var withFrozenEvent = WithUnrelatedFrozenAcceptedEvent(inputs);
        inputs = withFrozenEvent.Inputs;
        var frozenEventPath = withFrozenEvent.EventPath;
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var environment = BuildCoverEnvironment(
            temporary.Path,
            inputs,
            inputs.Files,
            RawChangeSet.Create([frozenEventPath]));

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.NotEqual(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        AssertUnreferencedAtomBytesUnchanged(temporary.Path, inputs, CoverWorld.UnrelatedAtomId);
    }

    [Fact]
    public void CoverAtomIgnoresByteIdenticalUnreferencedInvalidCoverage()
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomGid = "D5/S0/Carrier/Probe.sibling",
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
        });
        var inputs = DirectoryInputs(WithInvalidSiblingCoverageAtBaseline(
            materialized,
            byteIdenticalBaseline: true));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.NotEqual(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        AssertUnreferencedAtomBytesUnchanged(temporary.Path, inputs, CoverWorld.OtherAtomId);
    }

    private static (CoverInputs Inputs, string EventPath) WithUnrelatedFrozenAcceptedEvent(
        CoverInputs inputs)
    {
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        var existingPaths = files.Keys.ToHashSet(StringComparer.Ordinal);
        FrozenStatementReceiptTestData.AddLedger(
            files,
            new FrozenStatementReceiptTestData.Module(
                "D5/S9/Unrelated/FrozenBacklog.lean",
                FrozenStatementReceiptTestData.Id('9'),
                []));
        var eventPath = Assert.Single(
            files.Keys.Except(existingPaths, StringComparer.Ordinal),
            FrozenLedgerChangeClassifier.IsAcceptedEventPath);
        return (inputs with { Files = files }, eventPath);
    }
}
