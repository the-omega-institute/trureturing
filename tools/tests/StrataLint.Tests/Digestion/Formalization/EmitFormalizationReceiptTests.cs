using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// The producer side of the digestion-formalization-v1 pre-commitment (spec §11.21):
// `emit-formalization-receipt` reads the atom's fingerprint from BACKFILL and the
// declaration's canonical signature from the raw Lean report, then writes a
// canonical receipt that the cover transaction consumes via --envelope. These
// tests pin the round-trip (emit -> loader/cover accept), the end-to-end deposit
// (emit -> cover with an honest --base, no --base <deposit-origin> workaround), and
// the fail-closed rejects.
public sealed class EmitFormalizationReceiptTests
{
    [Fact]
    public void EmitReadsTheDirectoryFormDigestionLedger()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        var directoryInputs = inputs with
        {
            Files = DirectoryLedgerTestSupport.Project(inputs.Files),
            Baseline = DirectoryLedgerTestSupport.Project(inputs.Baseline),
        };
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, directoryInputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("FORMALIZATION_RECEIPT", result.Output, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar))));
    }

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
    public void CandidateFormalizationReceiptWriteGateRejectsNoncanonicalJson()
    {
        const string path = "Meta/Digestion/formalizations/candidate.v1.json";
        var canonical = DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            "candidate",
            "D5/S0/Carrier/Probe.probe",
            new DigestionFormalizationSignature("probe", "theorem", "True"),
            "sha256:" + new string('a', 64),
            "sha256:" + new string('a', 64)));
        var noncanonical = Encoding.UTF8.GetString(canonical.AsSpan()).Replace(
            "\": ",
            "\":",
            StringComparison.Ordinal);
        var snapshot = DigestionTestSupport.Snapshot((path, Encoding.UTF8.GetBytes(noncanonical)));

        var exception = Assert.Throws<FormatException>(() =>
            DigestionFormalizationReceipt.Load(snapshot, path));

        Assert.Contains("not canonical JSON", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EmitExtendsAnExistingReceiptWithARecomputedSecondarySignature()
    {
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryDeclaration = "window_register_crt_decomposition";
        var secondaryGid = secondaryModule + "." + secondaryDeclaration;
        var inputs = CoverWorld.Materialize(new CoverSpec
        {
            InitialCoverage = ImmutableArray.Create("D5/S0/Carrier/Probe.probe"),
            IncludeEnvelope = true,
            SecondaryTarget = (secondaryModule, secondaryDeclaration),
            IncludeSecondaryPrecommittedSignature = false,
        });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId,
                "--gid", inputs.Gid,
                "--gid", secondaryGid]);

        Assert.True(result.Success, result.Error);
        var relativeOut = "Meta/Digestion/formalizations/" + CoverWorld.DefaultAtomId + ".v1.json";
        using var document = JsonDocument.Parse(
            TemporaryFileSystem.File.ReadAllBytes(Path.Combine(temporary.Path, relativeOut)));
        var root = document.RootElement;
        Assert.Equal(inputs.Gid, root.GetProperty("primary_gid").GetString());
        var extension = Assert.Single(root.GetProperty("hosted_extensions").EnumerateArray());
        Assert.Equal(secondaryGid, extension.GetProperty("gid").GetString());
        var signature = extension.GetProperty("precommitted_signature");
        Assert.Equal(secondaryDeclaration, signature.GetProperty("name_key").GetString());
        Assert.Equal("theorem", signature.GetProperty("kind").GetString());
        Assert.Equal("True", signature.GetProperty("type").GetString());
    }

    [Fact]
    public void EmitCreatesAReceiptWithMultiplePrecommittedGidsBeforeCoverage()
    {
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryDeclaration = "window_register_crt_decomposition";
        var secondaryGid = secondaryModule + "." + secondaryDeclaration;
        var inputs = CoverWorld.Materialize(new CoverSpec
        {
            IncludeEnvelope = false,
            SecondaryTarget = (secondaryModule, secondaryDeclaration),
        });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId,
                "--gid", inputs.Gid,
                "--gid", secondaryGid]);

        Assert.True(result.Success, result.Error);
        var relativeOut = "Meta/Digestion/formalizations/" + CoverWorld.DefaultAtomId + ".v1.json";
        var receipt = DigestionFormalizationReceipt.Load(
            DigestionTestSupport.Snapshot((relativeOut,
                TemporaryFileSystem.File.ReadAllBytes(Path.Combine(temporary.Path, relativeOut)))),
            relativeOut);
        Assert.Equal(inputs.Gid, receipt.PrimaryGid);
        var extension = Assert.Single(receipt.HostedExtensions);
        Assert.Equal(secondaryGid, extension.Gid);
        Assert.Equal(secondaryDeclaration, extension.Signature.NameKey);
    }

    [Fact]
    public void EmitRegistersASecondGidBeforeTheFirstGidIsCovered()
    {
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryDeclaration = "window_register_crt_decomposition";
        var secondaryGid = secondaryModule + "." + secondaryDeclaration;
        var inputs = CoverWorld.Materialize(new CoverSpec
        {
            IncludeEnvelope = true,
            SecondaryTarget = (secondaryModule, secondaryDeclaration),
            IncludeSecondaryPrecommittedSignature = false,
        });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", secondaryGid]);

        Assert.True(result.Success, result.Error);
        var relativeOut = "Meta/Digestion/formalizations/" + CoverWorld.DefaultAtomId + ".v1.json";
        var receipt = DigestionFormalizationReceipt.Load(
            DigestionTestSupport.Snapshot((relativeOut,
                TemporaryFileSystem.File.ReadAllBytes(Path.Combine(temporary.Path, relativeOut)))),
            relativeOut);
        Assert.Equal(inputs.Gid, receipt.PrimaryGid);
        var extension = Assert.Single(receipt.HostedExtensions);
        Assert.Equal(secondaryGid, extension.Gid);
        Assert.Equal(secondaryDeclaration, extension.Signature.NameKey);
    }

    [Fact]
    public void EmitAcceptsAtomDerivedTemporaryOutPath()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);
        var relativeOut = "Meta/Digestion/formalizations/"
            + CoverWorld.DefaultAtomId
            + ".v1.json.tmp.fixture123";

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
                "--out", relativeOut]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("out=" + relativeOut, result.Output, StringComparison.Ordinal);
        Assert.True(File.Exists(Path.Combine(temporary.Path, relativeOut)));
        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            DigestionFormalizationReceipt.PathForAtom(CoverWorld.DefaultAtomId))));
    }

    [Fact]
    public void EmitRejectsAbsoluteOutPathEvenInsideCanonicalDirectory()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);
        var absoluteOut = Path.Combine(
            temporary.Path,
            DigestionFormalizationReceipt.PathForAtom(CoverWorld.DefaultAtomId)
                + ".tmp.absolute");

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
                "--out", absoluteOut]);

        Assert.False(result.Success);
        Assert.Contains("--out must be repository-relative", result.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(absoluteOut));
    }

    [Fact]
    public void EmitRejectsOutPathThatNormalizesOutsideCanonicalDirectory()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);
        var relativeOut = "Meta/Digestion/formalizations/../../../escape/"
            + CoverWorld.DefaultAtomId
            + ".v1.json.tmp.traversal";
        var escapedOut = Path.Combine(
            temporary.Path,
            "escape",
            CoverWorld.DefaultAtomId + ".v1.json.tmp.traversal");

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
                "--out", relativeOut]);

        Assert.False(result.Success);
        Assert.Contains(
            "--out must resolve directly under Meta/Digestion/formalizations/",
            result.Error,
            StringComparison.Ordinal);
        Assert.False(File.Exists(escapedOut));
    }

    [Fact]
    public void EmitRejectsAnotherAtomsCanonicalOutPath()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);
        const string relativeOut = "Meta/Digestion/formalizations/neighbour.v1.json";

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
                "--out", relativeOut]);

        Assert.False(result.Success);
        Assert.Contains(
            $"--out must name {CoverWorld.DefaultAtomId}.v1.json or "
            + $"{CoverWorld.DefaultAtomId}.v1.json.tmp.<suffix>",
            result.Error,
            StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(temporary.Path, relativeOut)));
    }

    [Fact]
    public void EmitRejectsBlankExplicitOutInsteadOfFallingBackToCanonical()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
                "--out", ""]);

        Assert.False(result.Success);
        Assert.Contains("--out must not be empty", result.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            DigestionFormalizationReceipt.PathForAtom(CoverWorld.DefaultAtomId))));
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
        var files = DirectoryLedgerTestSupport.Project(new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal)
        {
            [relativeOut] = receiptText,
        });
        var baseline = DirectoryLedgerTestSupport.Project(new Dictionary<string, string>(inputs.Baseline, StringComparer.Ordinal)
        {
            [relativeOut] = receiptText,
        });
        DirectoryLedgerTestSupport.Write(temporary.Path, files);
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
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries(),
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

    private static ProductionCliEnvironment BuildEmitEnvironment(string repositoryRoot, CoverInputs inputs)
    {
        var directoryInputs = inputs with
        {
            Files = DirectoryLedgerTestSupport.Project(inputs.Files),
            Baseline = DirectoryLedgerTestSupport.Project(inputs.Baseline),
        };
        return new(
            repositoryRoot,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(directoryInputs.Files),
                CoverWorld.Raw(directoryInputs.Baseline)),
            new FakeLeanReportSource(directoryInputs.Report));
    }

    private static class TemporaryFileSystem
    {
        internal static class File
        {
            internal static byte[] ReadAllBytes(string path) => System.IO.File.ReadAllBytes(path);
        }
    }
}
