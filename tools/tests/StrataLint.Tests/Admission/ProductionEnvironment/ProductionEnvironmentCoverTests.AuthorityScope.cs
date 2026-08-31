using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CoverAtomIgnoresUnchangedBadReceiptOutsideBaseOwnedFrozenClosure()
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
            "coverage-receipt-mismatch"));
        var withFrozenEvent = WithUnrelatedFrozenAcceptedEvent(inputs);
        inputs = withFrozenEvent.Inputs;
        var frozenEventPath = withFrozenEvent.EventPath;
        var backlogAtom = Assert.Single(inputs.Files, pair => pair.Key.EndsWith(
            "/" + CoverWorld.UnrelatedAtomId + ".yaml",
            StringComparison.Ordinal));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var environment = BuildCoverEnvironment(
            temporary.Path,
            inputs,
            inputs.Files,
            RawChangeSet.Create([frozenEventPath]));

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain(
            CoverWorld.UnrelatedAtomId + ":coverage-receipt-mismatch",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains(
            backlogAtom.Key
            + "\0"
            + Convert.ToBase64String(Encoding.UTF8.GetBytes(backlogAtom.Value))
            + "\n",
            DirectoryLedgerTestSupport.Image(temporary.Path),
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void CoverAtomIgnoresUnchangedReceiptIntegrityBacklogAtForkPoint(
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
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.NotEqual(before, DirectoryLedgerTestSupport.Image(temporary.Path));
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
        var eventPath = Assert.Single(files.Keys.Except(existingPaths, StringComparer.Ordinal));
        return (inputs with { Files = files }, eventPath);
    }
}
