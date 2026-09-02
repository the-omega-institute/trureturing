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
    private const string PreviousRenderedType = "Old.True";
    private const string LegacyUsageError =
        "FORMALIZATION_RECEIPT_INVALID USAGE: StrataLint emit-formalization-receipt "
        + "--atom-id ATOM_ID --gid PRIMARY_GID [--gid SECONDARY_GID ...] "
        + "[--out RECEIPT_PATH]\n";

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
    public void EmitReanchorsOnlyTypeWhenExplicitAndPropositionSourceEquivalent()
    {
        var inputs = ReanchorInputs(ReanchorSpec());
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);
        var previous = inputs.Files[inputs.EnvelopePath];
        var oldField = $"\"type\": \"{PreviousRenderedType}\"";
        const string newField = "\"type\": \"True\"";
        Assert.Equal(1, previous.Split(oldField, StringSplitOptions.None).Length - 1);

        var result = environment.EmitFormalizationReceipt(ReanchorArguments(inputs));

        Assert.True(result.Success, result.Error);
        var actual = File.ReadAllText(Path.Combine(temporary.Path, inputs.EnvelopePath));
        Assert.Equal(previous.Replace(oldField, newField, StringComparison.Ordinal), actual);
    }

    [Fact]
    public void EmitReanchorsHostedExtensionTypeAndPreservesOtherFields()
    {
        const string hostedDeclaration = "hosted_probe";
        const string hostedNameKey = "ns(n0,12:hosted_probe)";
        var hostedGid = "D5/S0/Carrier/Probe." + hostedDeclaration;
        var inputs = ReanchorInputs(ReanchorSpec() with
        {
            ReportDeclarations = ["probe", hostedDeclaration],
            AdditionalHostedExtensions =
            [
                new DigestionFormalizationExtension(
                    hostedGid,
                    new DigestionFormalizationSignature(
                        hostedNameKey,
                        "theorem",
                        PreviousRenderedType)),
            ],
        });
        inputs = inputs with
        {
            Report = LeanAxiomReport.Create(inputs.Report.Files.ToDictionary(
                static item => item.Key.Value,
                item => new LeanFileReport(
                    item.Value.Imports,
                    item.Value.Declarations.Select(declaration =>
                        string.Equals(declaration.Name, hostedDeclaration, StringComparison.Ordinal)
                            ? declaration with { NameKey = hostedNameKey }
                            : declaration).ToImmutableArray(),
                    item.Value.Error),
                StringComparer.Ordinal)),
        };
        var targetPath = "D5/S0/Carrier/Probe.lean";
        var targetSource = inputs.Files[targetPath]
            + $"\ntheorem {hostedDeclaration} : True := by trivial\n";
        inputs.Files[targetPath] = targetSource;
        inputs.Baseline[targetPath] = targetSource;
        using var temporary = new TemporaryDirectory();
        var previous = inputs.Files[inputs.EnvelopePath];
        var oldField = $"\"type\": \"{PreviousRenderedType}\"";
        const string newField = "\"type\": \"True\"";
        Assert.Equal(2, previous.Split(oldField, StringSplitOptions.None).Length - 1);

        var result = BuildEmitEnvironment(temporary.Path, inputs)
            .EmitFormalizationReceipt(ReanchorArguments(inputs));

        Assert.True(result.Success, result.Error);
        var actual = File.ReadAllText(Path.Combine(temporary.Path, inputs.EnvelopePath));
        Assert.Equal(previous.Replace(oldField, newField, StringComparison.Ordinal), actual);
        var receipt = DigestionFormalizationReceipt.Load(
            DigestionTestSupport.Snapshot((inputs.EnvelopePath, Encoding.UTF8.GetBytes(actual))),
            inputs.EnvelopePath);
        var extension = Assert.Single(receipt.HostedExtensions);
        Assert.Equal(hostedGid, extension.Gid);
        Assert.Equal(hostedNameKey, extension.Signature.NameKey);
        Assert.Equal("theorem", extension.Signature.Kind);
        Assert.Equal("True", extension.Signature.Type);
    }

    [Fact]
    public void EmitReanchorRejectsCurrentHostedAppendMixedWithPrimaryTypeChangeWithoutWriting()
    {
        const string hostedModule = "D5/S3/Observer/WindowRegisterCRT";
        const string hostedDeclaration = "window_register_crt_decomposition";
        var hostedGid = hostedModule + "." + hostedDeclaration;
        var inputs = ReanchorInputs(ReanchorSpec() with
        {
            SecondaryTarget = (hostedModule, hostedDeclaration),
            IncludeSecondaryPrecommittedSignature = false,
        });
        Assert.True(Gid.TryParse(hostedGid, out var parsedHostedGid));
        var currentReceipt = DigestionFormalizationReceipt.Load(
            DigestionTestSupport.Snapshot((
                inputs.EnvelopePath,
                Encoding.UTF8.GetBytes(inputs.Files[inputs.EnvelopePath]))),
            inputs.EnvelopePath);
        var hostedSignature = DigestionFormalizationReceipt.ResolveSignature(
            parsedHostedGid,
            inputs.Report);
        inputs.Files[inputs.EnvelopePath] = Encoding.UTF8.GetString(
            DigestionFormalizationReceipt.Write(currentReceipt with
            {
                HostedExtensions =
                [
                    new DigestionFormalizationExtension(hostedGid, hostedSignature),
                ],
            }).AsSpan());
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, inputs.EnvelopePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        var before = Encoding.UTF8.GetBytes(inputs.Files[inputs.EnvelopePath]);
        File.WriteAllBytes(outputPath, before);

        var result = BuildEmitEnvironment(temporary.Path, inputs)
            .EmitFormalizationReceipt(ReanchorArguments(inputs));

        Assert.False(result.Success);
        Assert.Contains("unchanged hosted_extensions gid set", result.Error, StringComparison.Ordinal);
        Assert.True(before.AsSpan().SequenceEqual(File.ReadAllBytes(outputPath)));
    }

    [Fact]
    public void EmitReanchorRejectsChangedNameKey()
    {
        var inputs = ReanchorInputs(ReanchorSpec() with
        {
            PrecommittedSignature = new DigestionFormalizationSignature(
                "renamed_probe",
                "theorem",
                PreviousRenderedType),
        });

        var result = ExecuteReanchor(inputs);

        Assert.False(result.Success);
        Assert.Equal(
            $"FORMALIZATION_RECEIPT_INVALID reanchor requires unchanged signature name_key "
            + $"for {inputs.Gid}\n",
            result.Error);
    }

    [Fact]
    public void EmitReanchorRejectsChangedKindWithUnchangedNameKey()
    {
        var inputs = ReanchorInputs(ReanchorSpec() with
        {
            PrecommittedSignature = new DigestionFormalizationSignature(
                "ns(n0,5:probe)",
                "def",
                PreviousRenderedType),
        });

        var result = ExecuteReanchor(inputs);

        Assert.False(result.Success);
        Assert.Equal(
            $"FORMALIZATION_RECEIPT_INVALID reanchor requires unchanged signature kind "
            + $"for {inputs.Gid}\n",
            result.Error);
    }

    [Fact]
    public void EmitReanchorRejectsChangedAtomIdBinding()
    {
        var inputs = ReanchorInputs(ReanchorSpec() with
        {
            EnvelopeAtomId = new string('a', 64),
        });

        var result = ExecuteReanchor(inputs);

        Assert.False(result.Success);
        Assert.Equal(
            "FORMALIZATION_RECEIPT_INVALID reanchor requires unchanged atom_id\n",
            result.Error);
    }

    [Fact]
    public void EmitReanchorRejectsChangedCasRefBinding()
    {
        var inputs = ReanchorInputs(ReanchorSpec() with
        {
            EnvelopeCasRef = "sha256:" + new string('b', 64),
        });

        var result = ExecuteReanchor(inputs);

        Assert.False(result.Success);
        Assert.Equal(
            "FORMALIZATION_RECEIPT_INVALID reanchor requires unchanged cas_ref\n",
            result.Error);
    }

    [Fact]
    public void EmitReanchorRejectsChangedRawSha256Binding()
    {
        var inputs = ReanchorInputs(ReanchorSpec() with
        {
            EnvelopeRawSha256 = "sha256:" + new string('c', 64),
        });

        var result = ExecuteReanchor(inputs);

        Assert.False(result.Success);
        Assert.Equal(
            "FORMALIZATION_RECEIPT_INVALID reanchor requires unchanged raw_sha256\n",
            result.Error);
    }

    [Fact]
    public void EmitReanchorRejectsPrimaryGidDifferentFromCommandLineGid()
    {
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryDeclaration = "window_register_crt_decomposition";
        var secondaryGid = secondaryModule + "." + secondaryDeclaration;
        var inputs = ReanchorInputs(ReanchorSpec() with
        {
            SecondaryTarget = (secondaryModule, secondaryDeclaration),
        });

        var result = ExecuteReanchor(inputs, primaryGid: secondaryGid);

        Assert.False(result.Success);
        Assert.Equal(
            $"FORMALIZATION_RECEIPT_INVALID reanchor requires --gid to equal existing "
            + $"primary_gid: {inputs.Gid}\n",
            result.Error);
    }

    [Fact]
    public void EmitReanchorRejectsChangedHostedExtensionGidSet()
    {
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryDeclaration = "window_register_crt_decomposition";
        var secondaryGid = secondaryModule + "." + secondaryDeclaration;
        var inputs = ReanchorInputs(ReanchorSpec() with
        {
            SecondaryTarget = (secondaryModule, secondaryDeclaration),
            IncludeSecondaryPrecommittedSignature = false,
        });

        var result = ExecuteReanchor(inputs, [secondaryGid]);

        Assert.False(result.Success);
        Assert.Equal(
            "FORMALIZATION_RECEIPT_INVALID reanchor requires unchanged "
            + "hosted_extensions gid set\n",
            result.Error);
    }

    [Fact]
    public void EmitReanchorRejectsInequivalentPropositionSource()
    {
        var inputs = ReanchorInputs(ReanchorSpec());
        Assert.True(Gid.TryParse(inputs.Gid, out var gid));
        var targetPath = gid.Path.Value;
        inputs.Files[targetPath] = inputs.Files[targetPath].Replace(
            "theorem probe : True",
            "theorem probe : False",
            StringComparison.Ordinal);

        var result = ExecuteReanchor(inputs);

        Assert.False(result.Success);
        Assert.Contains(
            "reanchor requires equivalent Lean proposition source",
            result.Error,
            StringComparison.Ordinal);
    }

    [Fact]
    public void EmitRejectsChangedExistingSignatureWithoutExplicitReanchorMode()
    {
        var inputs = ReanchorInputs(ReanchorSpec());
        using var temporary = new TemporaryDirectory();
        var environment = BuildEmitEnvironment(temporary.Path, inputs);

        var result = environment.EmitFormalizationReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid]);

        Assert.False(result.Success);
        Assert.Contains(
            $"existing formalization receipt signature changed for {inputs.Gid}",
            result.Error,
            StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(temporary.Path, inputs.EnvelopePath)));
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

    [Fact]
    public void EmitWithoutReanchorModeAndWithBaseUsesLegacyUsageBytes()
    {
        AssertLegacyUsage(
            ["--atom-id", CoverWorld.DefaultAtomId,
                "--gid", "D5/S0/Carrier/Probe.probe",
                "--base", "HEAD"]);
    }

    [Fact]
    public void EmitWithoutReanchorModeAndWithMissingValueUsesLegacyUsageBytes()
    {
        AssertLegacyUsage(
            ["--atom-id", CoverWorld.DefaultAtomId,
                "--gid", "D5/S0/Carrier/Probe.probe",
                "--base"]);
    }

    [Fact]
    public void EmitWithoutReanchorModeAndWithDuplicateArgumentUsesLegacyUsageBytes()
    {
        AssertLegacyUsage(
            ["--atom-id", CoverWorld.DefaultAtomId,
                "--gid", "D5/S0/Carrier/Probe.probe",
                "--atom-id", CoverWorld.DefaultAtomId]);
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

    private static CoverSpec ReanchorSpec() => new()
    {
        IncludeEnvelope = true,
        BaselineTargetIdentical = true,
        PrecommittedSignature = new DigestionFormalizationSignature(
            "ns(n0,5:probe)",
            "theorem",
            PreviousRenderedType),
    };

    private static CoverInputs ReanchorInputs(CoverSpec spec)
    {
        var inputs = CoverWorld.Materialize(spec);
        var report = LeanAxiomReport.Create(inputs.Report.Files.ToDictionary(
            static item => item.Key.Value,
            static item => new LeanFileReport(
                item.Value.Imports,
                item.Value.Declarations.Select(static declaration =>
                    string.Equals(declaration.Name, "probe", StringComparison.Ordinal)
                        ? declaration with { NameKey = "ns(n0,5:probe)" }
                        : declaration).ToImmutableArray(),
                item.Value.Error),
            StringComparer.Ordinal));
        return inputs with { Report = report };
    }

    private static IReadOnlyList<string> ReanchorArguments(
        CoverInputs inputs,
        IReadOnlyList<string>? additionalGids = null,
        string? primaryGid = null)
    {
        var arguments = new List<string>
        {
            "--atom-id", CoverWorld.DefaultAtomId,
            "--gid", primaryGid ?? inputs.Gid,
        };
        foreach (var gid in additionalGids ?? [])
        {
            arguments.Add("--gid");
            arguments.Add(gid);
        }

        arguments.Add("--reanchor-signature");
        arguments.Add("--base");
        arguments.Add("baseline");
        return arguments;
    }

    private static CommandResult ExecuteReanchor(
        CoverInputs inputs,
        IReadOnlyList<string>? additionalGids = null,
        string? primaryGid = null)
    {
        using var temporary = new TemporaryDirectory();
        return BuildEmitEnvironment(temporary.Path, inputs)
            .EmitFormalizationReceipt(ReanchorArguments(inputs, additionalGids, primaryGid));
    }

    private static void AssertLegacyUsage(IReadOnlyList<string> arguments)
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { IncludeEnvelope = false });
        using var temporary = new TemporaryDirectory();

        var result = BuildEmitEnvironment(temporary.Path, inputs)
            .EmitFormalizationReceipt(arguments);

        Assert.False(result.Success);
        Assert.Equal(LegacyUsageError, result.Error);
    }

    private static class TemporaryFileSystem
    {
        internal static class File
        {
            internal static byte[] ReadAllBytes(string path) => System.IO.File.ReadAllBytes(path);
        }
    }
}
