using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void ReceiptRealignmentClearsMixedBacklogAndPreservesLedgerIdentity()
    {
        var inputs = MixedReceiptBacklogInputs();
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = inputs.Document.RequireDigestionEntries()
            .Single(static entry => entry.AtomId == "receipt-gap-sibling");
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.RealignReceipts(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("fatal_gaps_repaired=3", result.Output, StringComparison.Ordinal);
        Assert.Contains("coverage_receipts_changed=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("scribe_receipts_changed=1", result.Output, StringComparison.Ordinal);
        var after = BackfillInventoryLoader.LoadRoot(temporary.Path)
            .RequireDigestionEntries()
            .Single(static entry => entry.AtomId == "receipt-gap-sibling");
        Assert.Equal(before.SourceId, after.SourceId);
        Assert.Equal(before.SourcePath, after.SourcePath);
        Assert.Equal(before.Atomizer, after.Atomizer);
        Assert.Equal(before.AtomId, after.AtomId);
        Assert.Equal(before.AstPath, after.AstPath);
        Assert.Equal(before.Boundary, after.Boundary);
        Assert.Equal(before.Fingerprints, after.Fingerprints);
        Assert.Equal(before.CoverageGids.ToArray(), after.CoverageGids.ToArray());
        Assert.Equal(before.CasRef, after.CasRef);
        Assert.Equal(
            before.Receipts.UnresolvedSubitems.ToArray(),
            after.Receipts.UnresolvedSubitems.ToArray());
        Assert.Equal(before.Receipts.ChainAtoms.ToArray(), after.Receipts.ChainAtoms.ToArray());
        Assert.Equal(before.Receipts.TailAuthorization, after.Receipts.TailAuthorization);
        Assert.Equal(before.Receipts.Quarantine, after.Receipts.Quarantine);
        Assert.Equal(before.Receipts.Coverage.Select(static item => item.Gid),
            after.Receipts.Coverage.Select(static item => item.Gid));
        Assert.Equal(before.Receipts.Scribe.Select(static item => item.Gid),
            after.Receipts.Scribe.Select(static item => item.Gid));

        var alignedFiles = FilesWithLedgerFromRoot(inputs.Files, temporary.Path);
        var status = BuildCoverEnvironment(temporary.Path, inputs, alignedFiles)
            .DigestStatus(Array.Empty<string>());
        Assert.True(status.Success, status.Error);
    }

    [Fact]
    public void ReceiptRealignmentRejectsDuplicateReceiptWithoutWriting()
    {
        var inputs = WithDuplicateScribeReceipt(MixedReceiptBacklogInputs());
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files)
            .RealignReceipts(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("must have exactly one Scribe receipt", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Fact]
    public void ReceiptRealignmentRejectsRemainingFatalGapWithoutWriting()
    {
        var inputs = MixedReceiptBacklogInputs();
        var gid = inputs.Document.RequireDigestionEntries()
            .Single(static entry => entry.AtomId == "receipt-gap-sibling")
            .CoverageGids.Single();
        var documentGid = ScribeEmissionAttestation.DocumentGid(gid);
        Assert.True(inputs.VerifiedEmissions!.TryGet(documentGid, out var verified));
        var inconsistentVerification = VerifiedScribeEmissions.Create(
        [
            verified with
            {
                DefinitionSha256 = "sha256:" + new string('e', 64),
            },
        ],
        [gid]);
        inputs = inputs with { VerifiedEmissions = inconsistentVerification };
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files)
            .RealignReceipts(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("scribe-definition-mismatch", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    private static CoverInputs MixedReceiptBacklogInputs()
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomBinding = ("receipt-gap-sibling", "D5/S0/Carrier/Probe.sibling"),
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
        });
        const string atomId = "receipt-gap-sibling";
        var entry = materialized.Document.RequireDigestionEntries()
            .Single(static item => item.AtomId == atomId);
        var gid = Assert.Single(entry.CoverageGids);
        var stale = "sha256:" + new string('c', 64);
        var document = materialized.Document.WithDigestionSources(
            materialized.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(item => item.AtomId == atomId
                        ? item with
                        {
                            Receipts = item.Receipts with
                            {
                                Coverage =
                                [
                                    new DigestionCoverageReceipt(gid, stale, stale),
                                ],
                                Scribe =
                                [
                                    new DigestionScribeReceipt(gid, stale, stale),
                                ],
                            },
                        }
                        : item).ToImmutableArray(),
                })
                .ToImmutableArray());
        var files = new Dictionary<string, string>(materialized.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        var baseline = new Dictionary<string, string>(files, StringComparer.Ordinal);
        var documentGid = ScribeEmissionAttestation.DocumentGid(gid);
        Assert.True(materialized.VerifiedEmissions!.TryGet(documentGid, out var verified));
        return DirectoryInputs(materialized with
        {
            Files = files,
            Baseline = baseline,
            Document = document,
            VerifiedEmissions = VerifiedScribeEmissions.Create(
                [verified],
                [materialized.Gid, gid]),
        });
    }

    private static CoverInputs WithDuplicateScribeReceipt(CoverInputs inputs)
    {
        const string atomId = "receipt-gap-sibling";
        var document = inputs.Document.WithDigestionSources(
            inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == atomId
                        ? entry with
                        {
                            Receipts = entry.Receipts with
                            {
                                Scribe = entry.Receipts.Scribe.Add(
                                    Assert.Single(entry.Receipts.Scribe)),
                            },
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        return inputs with { Files = files, Document = document };
    }
}
