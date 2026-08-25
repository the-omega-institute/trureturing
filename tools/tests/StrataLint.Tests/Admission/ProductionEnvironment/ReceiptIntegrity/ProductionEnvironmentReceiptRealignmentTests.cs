using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
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
    public void ReceiptRealignmentRejectsCandidateCoverageClaimReplacementWithoutWriting()
    {
        var inputs = WithCandidateCoverageClaimReplacement(MixedReceiptBacklogInputs());
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files)
            .RealignReceipts(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("coverage claim changed", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Fact]
    public void ReceiptRealignmentRejectsChangedLeanDeclarationSignatureWithoutWriting()
    {
        var inputs = WithChangedDeclarationSignature(
            DirectoryInputs(CoverWorld.Materialize(CoverWorld.StaleReceiptSpec())),
            "probe");
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files)
            .RealignReceipts(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("Lean declaration signature changed", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Fact]
    public void ReceiptRealignmentRejectsBaselineFormalizationReceiptForDifferentAtomWithoutWriting()
    {
        var inputs = WithBaselineFormalizationReceipt(
            DirectoryInputs(CoverWorld.Materialize(CoverWorld.StaleReceiptSpec())),
            receiptAtomId: "different-atom");
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files)
            .RealignReceipts(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains(
            "baseline formalization receipt has a different atom_id",
            result.Error,
            StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Fact]
    public void ReceiptRealignmentRejectsCoverageGidMissingFromBaselineFormalizationReceiptWithoutWriting()
    {
        var materialized = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec() with
        {
            ReportDeclarations = ImmutableArray.Create("probe", "replacement"),
        });
        var inputs = WithBaselineFormalizationReceipt(
            DirectoryInputs(materialized),
            primaryGid: "D5/S0/Carrier/Probe.replacement");
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files)
            .RealignReceipts(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains(
            "baseline formalization receipt does not pin D5/S0/Carrier/Probe.probe",
            result.Error,
            StringComparison.Ordinal);
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

    [Fact]
    public void ReceiptRealignmentFinalFullScanRejectsCorruptedSerializedLedger()
    {
        var inputs = MixedReceiptBacklogInputs();
        var finalSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(CoverWorld.Raw(inputs.Files))).Snapshot;
        var baselineSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(CoverWorld.Raw(inputs.Baseline))).Snapshot;
        var finalDocument = BackfillInventoryLoader.Load(finalSnapshot);
        var baselineDocument = BackfillInventoryLoader.LoadBaseline(baselineSnapshot);
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(finalSnapshot, inputs.Report)).Capability;

        var exception = Assert.Throws<InvalidOperationException>(() =>
            IngestCommand.RequireFinalReceiptRealignmentFullScan(
                finalDocument,
                finalSnapshot,
                lean,
                inputs.VerifiedEmissions!,
                baselineDocument,
                baselineSnapshot));

        Assert.Contains("coverage-receipt-mismatch", exception.Message, StringComparison.Ordinal);
    }

    private static CoverInputs MixedReceiptBacklogInputs()
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomBinding = ("receipt-gap-sibling", "D5/S0/Carrier/Probe.sibling"),
            ReportDeclarations = ImmutableArray.Create("probe", "sibling", "replacement"),
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
        Assert.True(Gid.TryParse(gid, out var parsedGid));
        var formalizationPath = DigestionFormalizationReceipt.PathForAtom(atomId);
        files[formalizationPath] = Encoding.UTF8.GetString(
            DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
                atomId,
                gid,
                DigestionFormalizationReceipt.ResolveSignature(parsedGid, materialized.Report),
                entry.CasRef,
                entry.Fingerprints.RawSha256)).AsSpan());
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
                [materialized.Gid, gid, "D5/S0/Carrier/Probe.replacement"]),
        });
    }

    private static CoverInputs WithCandidateCoverageClaimReplacement(CoverInputs inputs)
    {
        const string atomId = "receipt-gap-sibling";
        const string replacementGid = "D5/S0/Carrier/Probe.replacement";
        var document = inputs.Document.WithDigestionSources(
            inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == atomId
                        ? entry with
                        {
                            CoverageGids = [replacementGid],
                            Receipts = entry.Receipts with
                            {
                                Coverage = entry.Receipts.Coverage
                                    .Select(receipt => receipt with { Gid = replacementGid })
                                    .ToImmutableArray(),
                                Scribe = entry.Receipts.Scribe
                                    .Select(receipt => receipt with { Gid = replacementGid })
                                    .ToImmutableArray(),
                            },
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        return inputs with { Files = files, Document = document };
    }

    private static CoverInputs WithChangedDeclarationSignature(
        CoverInputs inputs,
        string declarationName)
    {
        var files = inputs.Report.Files.ToDictionary(
            static pair => pair.Key.Value,
            pair => pair.Value with
            {
                Declarations = pair.Value.Declarations
                    .Select(declaration => declaration.Name == declarationName
                        ? declaration with { TypeRepresentation = "False" }
                        : declaration)
                    .ToImmutableArray(),
            },
            StringComparer.Ordinal);
        return inputs with { Report = LeanAxiomReport.Create(files) };
    }

    private static CoverInputs WithBaselineFormalizationReceipt(
        CoverInputs inputs,
        string? receiptAtomId = null,
        string? primaryGid = null)
    {
        var entry = Assert.Single(inputs.Document.RequireDigestionEntries());
        var pinnedGid = primaryGid ?? Assert.Single(entry.CoverageGids);
        Assert.True(Gid.TryParse(pinnedGid, out var parsedGid));
        var baseline = new Dictionary<string, string>(inputs.Baseline, StringComparer.Ordinal)
        {
            [DigestionFormalizationReceipt.PathForAtom(entry.AtomId)] = Encoding.UTF8.GetString(
                DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
                    receiptAtomId ?? entry.AtomId,
                    pinnedGid,
                    DigestionFormalizationReceipt.ResolveSignature(parsedGid, inputs.Report),
                    entry.CasRef,
                    entry.Fingerprints.RawSha256)).AsSpan()),
        };
        return inputs with { Baseline = baseline };
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
