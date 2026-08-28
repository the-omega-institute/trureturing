using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CoverAtomTests
{
    [Fact]
    public void AlignScribeReceiptPreservesInheritedAbsorbedSibling()
    {
        const string siblingAtomId = "historical-absorbed-sibling";
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec() with
        {
            OtherAtomBinding = (siblingAtomId, "D5/S0/Carrier/Probe.probe"),
        });
        inputs = WithHistoricalAbsorbedEntry(inputs, siblingAtomId, refreshScribeReceipt: true);

        var (result, document) = Align(inputs);

        Assert.True(result.Success, result.Error);
        var sibling = Assert.Single(
            document.RequireDigestionEntries(),
            entry => entry.AtomId == siblingAtomId);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            sibling.ProjectedStatus);
    }

    [Fact]
    public void AlignScribeReceiptRefreshesInheritedHistoricalAtom()
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        inputs = WithHistoricalAbsorbedEntry(
            inputs,
            CoverWorld.DefaultAtomId,
            refreshScribeReceipt: false);

        var (result, document) = Align(inputs);

        Assert.True(result.Success, result.Error);
        var target = Assert.Single(document.RequireDigestionEntries());
        Assert.Equal("theorem/historical", target.AstPath);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            target.ProjectedStatus);
    }

    private static CoverInputs WithHistoricalAbsorbedEntry(
        CoverInputs inputs,
        string atomId,
        bool refreshScribeReceipt)
    {
        Assert.True(inputs.VerifiedEmissions!.TryGet(
            ScribeEmissionAttestation.DocumentGid(inputs.Gid), out var verified));
        var document = inputs.Document.WithDigestionSources(
            inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == atomId
                        ? entry with
                        {
                            AstPath = atomId == CoverWorld.DefaultAtomId
                                ? "theorem/historical"
                                : entry.AstPath,
                            Receipts = refreshScribeReceipt
                                ? entry.Receipts with
                                {
                                    Scribe = entry.Receipts.Scribe.Select(receipt => receipt with
                                    {
                                        DefinitionSha256 = verified.DefinitionSha256,
                                        EmissionSha256 = verified.EmissionSha256,
                                    }).ToImmutableArray(),
                                }
                                : entry.Receipts,
                            ProjectedStatus = new DigestionStatus(
                                DigestionMigrationState.Absorbed,
                                DigestionTruthState.Closed),
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        DirectoryLedgerTestSupport.ReplaceWithProjection(currentFiles, document);
        return inputs with
        {
            Files = currentFiles,
            Baseline = new Dictionary<string, string>(currentFiles, StringComparer.Ordinal),
            Document = document,
        };
    }

    private static (CommandResult Result, BackfillInventoryDocument Document) Align(CoverInputs inputs)
    {
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var result = CoverWorld.Environment(temporary.Path, inputs, currentFiles)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));
        return (result, BackfillInventoryLoader.LoadRoot(temporary.Path));
    }
}
