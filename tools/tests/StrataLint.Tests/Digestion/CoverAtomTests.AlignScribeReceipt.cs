using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CoverAtomTests
{
    [Theory]
    [InlineData("probe")]
    [InlineData(null)]
    public void AlignScribeReceiptUsesVerifiedFingerprintsAndIsIdempotent(string? declaration)
    {
        var spec = CoverWorld.StaleReceiptSpec() with { Declaration = declaration };
        var inputs = CoverWorld.Materialize(spec with { InitialCoverage = [spec.Gid] });
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);

        var first = CoverWorld.Environment(temporary.Path, inputs, currentFiles)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.True(first.Success, first.Error);
        Assert.Contains("ALIGN_SCRIBE_RECEIPT", first.Output, StringComparison.Ordinal);
        Assert.Contains($"atom_id={CoverWorld.DefaultAtomId}", first.Output, StringComparison.Ordinal);
        Assert.Contains($"gid={inputs.Gid}", first.Output, StringComparison.Ordinal);
        Assert.Contains("old_definition_sha256=sha256:aaaaaaaa", first.Output, StringComparison.Ordinal);
        Assert.Contains("new_definition_sha256=sha256:", first.Output, StringComparison.Ordinal);
        Assert.Contains("old_emission_sha256=sha256:bbbbbbbb", first.Output, StringComparison.Ordinal);
        Assert.Contains("new_emission_sha256=sha256:", first.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", first.Output, StringComparison.Ordinal);
        var afterFirst = DirectoryLedgerTestSupport.Image(
            BackfillInventoryLoader.LoadRoot(temporary.Path));
        Assert.True(inputs.VerifiedEmissions!.TryGet(
            ScribeEmissionAttestation.DocumentGid(inputs.Gid), out var verifiedRecord));
        Assert.Equal(
            ExpectedAlignedScribeImage(inputs, verifiedRecord),
            afterFirst);

        var replayFiles = new Dictionary<string, string>(currentFiles, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(
            replayFiles,
            BackfillInventoryLoader.LoadRoot(temporary.Path));
        var second = CoverWorld.Environment(temporary.Path, inputs, replayFiles)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.True(second.Success, second.Error);
        Assert.Contains("ledger_changed=false", second.Output, StringComparison.Ordinal);
        Assert.Equal(
            afterFirst,
            DirectoryLedgerTestSupport.Image(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    [Theory]
    [InlineData(null, false)]
    [InlineData("probe", false)]
    [InlineData("probe", true)]
    public void AlignScribeReceiptRequiresVerifiedEmissionAndAnyDeclarationReference(
        string? declaration,
        bool includeEmission)
    {
        var spec = CoverWorld.StaleReceiptSpec() with { Declaration = declaration };
        var inputs = CoverWorld.Materialize(spec with { InitialCoverage = [spec.Gid] });
        Assert.True(inputs.VerifiedEmissions!.TryGet(spec.ModuleGid, out var record));
        inputs = inputs with
        {
            VerifiedEmissions = VerifiedScribeEmissions.Create(includeEmission ? [record] : []),
        };
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = CoverWorld.Environment(temporary.Path, inputs, inputs.Files)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains("has no verified Scribe emission", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Theory]
    [InlineData(null, 0, 1)]
    [InlineData(null, 2, 1)]
    [InlineData(null, 1, 0)]
    [InlineData(null, 1, 2)]
    [InlineData("probe", 0, 1)]
    [InlineData("probe", 2, 1)]
    [InlineData("probe", 1, 0)]
    [InlineData("probe", 1, 2)]
    public void AlignScribeReceiptRequiresExactlyOneExistingEdgeAndReceipt(
        string? declaration,
        int edgeCount,
        int receiptCount)
    {
        var spec = CoverWorld.StaleReceiptSpec() with { Declaration = declaration };
        var inputs = CoverWorld.Materialize(spec with { InitialCoverage = [spec.Gid] });
        var source = Assert.Single(inputs.Document.RequireDigestionSources());
        var entry = Assert.Single(source.Entries);
        var document = inputs.Document.WithDigestionSources([source with
        {
            Entries = [entry with
            {
                Coverage = Enumerable.Repeat(Assert.Single(entry.Coverage), edgeCount).ToImmutableArray(),
                Receipts = entry.Receipts with
                {
                    Scribe = Enumerable.Repeat(Assert.Single(entry.Receipts.Scribe), receiptCount)
                        .ToImmutableArray(),
                },
            }],
        }]);
        DirectoryLedgerTestSupport.ReplaceWithProjection(inputs.Files, document);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = CoverWorld.Environment(temporary.Path, inputs, inputs.Files)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains(edgeCount == 1 ? "exactly one Scribe receipt" : "exactly once",
            result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    public static TheoryData<string, string> UnknownAlignTargets => new()
    {
        { "no-such-atom", "D5/S0/Carrier/Probe.probe" },
        { CoverWorld.DefaultAtomId, "D5/S0/Carrier/Probe.missing" },
    };

    [Theory]
    [MemberData(nameof(UnknownAlignTargets))]
    public void AlignScribeReceiptFailsClosedForUnknownAtomOrGid(string atomId, string gid)
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));

        var result = CoverWorld.Environment(temporary.Path, inputs, inputs.Files).AlignScribeReceipt(
            ["--atom-id", atomId, "--gid", gid]);

        Assert.False(result.Success);
        Assert.Contains("ALIGN_SCRIBE_RECEIPT_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(inputs.Ledger, File.ReadAllText(outputPath));
    }

    [Fact]
    public void AlignScribeReceiptRejectsSiblingStatusDriftBeforeWritingLedger()
    {
        var spec = CoverWorld.StaleReceiptSpec() with
        {
            OtherAtomGid = "D5/S0/Carrier/Probe.sibling",
        };
        var inputs = CoverWorld.Materialize(spec);
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var before = DirectoryLedgerTestSupport.Image(BackfillInventoryLoader.LoadRoot(temporary.Path));
        var result = CoverWorld.Environment(temporary.Path, inputs, currentFiles)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));
        Assert.False(result.Success);
        Assert.Contains("digest status is invalid", result.Error, StringComparison.Ordinal);
        Assert.Contains(CoverWorld.OtherAtomId, result.Error, StringComparison.Ordinal);
        Assert.Equal(before,
            DirectoryLedgerTestSupport.Image(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }
}
