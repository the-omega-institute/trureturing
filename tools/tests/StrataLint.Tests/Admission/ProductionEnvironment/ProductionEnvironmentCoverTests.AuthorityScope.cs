using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CoverAtomValidatesCurrentCoverageOutsideBaseOwnedFrozenClosure()
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
        var inputs = DirectoryInputs(WithSiblingReceiptMismatch(
            materialized,
            "coverage-target-mismatch"));
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

        Assert.False(result.Success);
        Assert.Contains(
            CoverWorld.UnrelatedAtomId + ":coverage-target-mismatch",
            result.Error,
            StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Theory]
    [InlineData("coverage-target-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void CoverAtomAlwaysValidatesCurrentCoverageButScopesForkPointScribeBacklog(
        string mismatchCode)
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomGid = "D5/S0/Carrier/Probe.sibling",
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
        });
        var inputs = DirectoryInputs(WithReceiptMismatchAtForkPoint(
            materialized,
            mismatchCode,
            byteIdenticalBaseline: true));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        if (mismatchCode == "coverage-target-mismatch")
        {
            Assert.False(result.Success);
            Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
            Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        }
        else
        {
            Assert.True(result.Success, result.Error);
            Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
            Assert.NotEqual(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        }
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
