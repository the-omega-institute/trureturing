using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// The producer side of the digestion-formalization-v1 pre-commitment (spec §4a):
// `emit-formalization-receipt` reads the atom's fingerprint from BACKFILL and the
// declaration's canonical signature from the raw Lean report, then writes a
// canonical receipt that the cover transaction consumes via --envelope. These
// tests pin the round-trip (emit -> loader/cover accept), the end-to-end deposit
// (emit -> cover with an honest --base, no --base <deposit-origin> workaround), and
// the fail-closed rejects.
public sealed class EmitFormalizationReceiptTests
{
    [Fact]
    public void EmitWritesCanonicalReceiptTheLoaderAcceptsAndReWriteIsByteIdentical()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid]);

        Assert.True(result.Success, result.Error);
        var relativeOut = "Meta/Digestion/formalizations/" + CoverWorld.DefaultAtomId + ".v1.json";
        Assert.Contains("out=" + relativeOut, result.Output, StringComparison.Ordinal);
        Assert.Contains("signature=(probe, theorem, True)", result.Output, StringComparison.Ordinal);

        var outputPath = Path.Combine(temporary.Path, relativeOut);
        Assert.True(File.Exists(outputPath));
        var bytes = File.ReadAllBytes(outputPath);

        // The fail-closed loader accepts the emitted bytes (canonicality is verified
        // inside Load), and re-writing the loaded receipt is byte-identical.
        var snapshot = DigestionTestSupport.Snapshot((relativeOut, bytes));
        var receipt = DigestionFormalizationReceipt.Load(snapshot, relativeOut);
        Assert.Equal(CoverWorld.DefaultAtomId, receipt.AtomId);
        Assert.Equal(inputs.Gid, receipt.PrimaryGid);
        Assert.Equal("probe", receipt.Signature.NameKey);
        Assert.Equal("theorem", receipt.Signature.Kind);
        Assert.Equal("True", receipt.Signature.Type);
        Assert.True(DigestionFormalizationReceipt.Write(receipt).AsSpan().SequenceEqual(bytes));
    }

    [Fact]
    public void EmitHonorsAnExplicitOutPath()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
                "--out", "Meta/Digestion/formalizations/custom.json"]);

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(
            Path.Combine(temporary.Path, "Meta/Digestion/formalizations/custom.json")));
    }

    [Fact]
    public void EmittedReceiptDrivesCoverAtomEndToEndWithoutBaseWorkaround()
    {
        // Model the two-phase deposit: the covered declaration's Lean file is
        // base-owned (frozen in PR-1). PR-1 emits the pre-committed receipt; PR-2
        // covers with an honest `--base baseline` and the emitted --envelope.
        var inputs = CoverWorld.Materialize(new CoverSpec
        {
            IncludeEnvelope = false,
            BaselineTargetIdentical = true,
        });
        using var temporary = new TemporaryDirectory();

        // PR-1: emit the receipt (producer reads BACKFILL + Lean report).
        var emit = BuildEmitEnvironment(temporary.Path, inputs)
            .EmitFormalizationReceipt(["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid]);
        Assert.True(emit.Success, emit.Error);
        var relativeOut = "Meta/Digestion/formalizations/" + CoverWorld.DefaultAtomId + ".v1.json";
        var receiptText = File.ReadAllText(Path.Combine(temporary.Path, relativeOut));

        // PR-2: the committed receipt is now part of the snapshot; cover consumes it.
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal)
        {
            [relativeOut] = receiptText,
        };
        var baseline = new Dictionary<string, string>(inputs.Baseline, StringComparer.Ordinal)
        {
            [relativeOut] = receiptText,
        };
        var ledgerPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(ledgerPath)!);
        File.WriteAllText(ledgerPath, inputs.Ledger, new UTF8Encoding(false));
        var coverEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(files),
                CoverWorld.Raw(baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions));

        var cover = coverEnvironment.CoverAtom(
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
                "--base", "baseline", "--envelope", relativeOut]);

        Assert.True(cover.Success, cover.Error);
        Assert.Contains("ledger_changed=true", cover.Output, StringComparison.Ordinal);
        var entry = Assert.Single(
            BackfillInventoryLoader.Load(File.ReadAllText(ledgerPath)).RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal([inputs.Gid], entry.CoverageGids.ToArray());
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
    }

    [Fact]
    public void EmitRejectsAtomAbsentFromLedger()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", "no-such-atom", "--gid", inputs.Gid]);

        Assert.False(result.Success);
        Assert.Contains("FORMALIZATION_RECEIPT_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Contains("is absent from the ledger", result.Error, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(temporary.Path, "Meta/Digestion")));
    }

    [Fact]
    public void EmitRejectsGidWithoutDeclarationSelector()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", "D5/S0/Carrier/Probe"]);

        Assert.False(result.Success);
        Assert.Contains("must select a Lean declaration", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void EmitRejectsDeclarationAbsentFromLeanReport()
    {
        // The GID selector "probe" is not present in the raw Lean report, so the
        // signature cannot be pinned: fail closed rather than emit a receipt whose
        // pre-committed signature is unresolved.
        var inputs = CoverWorld.Materialize(new CoverSpec
        {
            IncludeEnvelope = false,
            ReportDeclarations = ImmutableArray.Create("unrelated"),
        });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid]);

        Assert.False(result.Success);
        Assert.Contains("resolves to 0 report declarations", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void EmitRejectsIncompleteArguments()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(["--atom-id", CoverWorld.DefaultAtomId]);

        Assert.False(result.Success);
        Assert.Contains("USAGE: StrataLint emit-formalization-receipt", result.Error, StringComparison.Ordinal);
    }

    private static ProductionCliEnvironment BuildEmitEnvironment(string repositoryRoot, CoverInputs inputs) =>
        new(
            repositoryRoot,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(inputs.Files),
                CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report));
}
