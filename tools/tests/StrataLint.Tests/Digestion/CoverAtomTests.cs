using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// Phase 1 cover transaction gate matrix. cover binds one already-proven Lean
// declaration to an existing open residual atom by writing coverage_gids +
// coverage/scribe receipts, all-or-nothing. Precondition and integrity rejects
// leave the ledger unchanged; a terminal initial-cover failure writes only its
// disposition. The envelope / pre-committed-receipt /
// declaration-signature gates (spec §11.21) live in the CoverAtomEnvelopeTests.cs
// partial (kept there so this file stays under the SL-003 800-line cap).
public sealed partial class CoverAtomTests
{
    [Fact]
    public void AlignScribeReceiptUsesVerifiedFingerprintsAndIsIdempotent()
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
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
            inputs.Gid[..inputs.Gid.LastIndexOf('.')], out var verifiedRecord));
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
    [InlineData("no-such-atom", "D5/S0/Carrier/Probe.probe")]
    [InlineData(CoverWorld.DefaultAtomId, "D5/S0/Carrier/Probe.missing")]
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
            OtherAtomBinding = ("drifted-sibling", "D5/S0/Carrier/Probe.sibling"),
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
        Assert.Contains("drifted-sibling", result.Error, StringComparison.Ordinal);
        Assert.Equal(before,
            DirectoryLedgerTestSupport.Image(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    [Fact]
    public void CoverBindsDeletableDeclarationAndWritesCoverageReceipts()
    {
        var (result, after, before, afterDocument) = Execute(new CoverSpec());

        Assert.True(result.Success, result.Error);
        Assert.Contains($"COVER atom_id={CoverWorld.DefaultAtomId}", result.Output, StringComparison.Ordinal);
        Assert.Contains("gid=D5/S0/Carrier/Probe.probe", result.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.NotEqual(before, after);

        var entry = Assert.Single(
            afterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal(["D5/S0/Carrier/Probe.probe"], entry.CoverageGids.ToArray());
        Assert.Single(entry.Receipts.Coverage);
        Assert.Single(entry.Receipts.Scribe);
        Assert.Equal(DigestionMigrationState.Absorbed, entry.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
    }

    [Fact]
    public void CoverRejectsAtomThatAlreadyHasCoverage()
    {
        var (result, after, before, _) = Execute(new CoverSpec
        {
            InitialCoverage = ImmutableArray.Create("D5/S0/Carrier/Probe.probe"),
        });

        Assert.False(result.Success);
        Assert.Contains("already has coverage", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsAtomThatIsNotOpen()
    {
        var (result, after, before, _) = Execute(new CoverSpec
        {
            Migration = "partial",
            Truth = "closed",
        });

        Assert.False(result.Success);
        Assert.Contains("is not open", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsAtomAbsentFromLedger()
    {
        var spec = new CoverSpec();
        var envelopePath = "Meta/Digestion/formalizations/" + spec.AtomId + ".v1.json";
        var (result, after, before, _) = Execute(
            spec,
            ["--cover-atom", "no-such-atom", "--gid", spec.Gid, "--base", "baseline",
                "--envelope", envelopePath]);

        Assert.False(result.Success);
        Assert.Contains("is absent", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsGidWithoutDeclarationSelector()
    {
        var (result, after, before, _) = Execute(new CoverSpec { Declaration = null });

        Assert.False(result.Success);
        Assert.Contains("must select a Lean declaration", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverAcceptsGidAlreadyBoundInBaselineLedger()
    {
        var execution = Execute(new CoverSpec
        {
            BaselineCoverageGid = "D5/S0/Carrier/Probe.probe",
            InitialDefinitionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256,
            InitialEmissionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256,
        });
        var (result, after, before) = execution;

        Assert.True(result.Success, result.Error);
        Assert.NotEqual(before, after);
        var entry = Assert.Single(
            execution.AfterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal(["D5/S0/Carrier/Probe.probe"], entry.CoverageGids.ToArray());
        Assert.Single(entry.Receipts.Coverage);
        Assert.Single(entry.Receipts.Scribe);
    }

    [Fact]
    public void CoverRejectsDeclarationAbsentFromLeanReportWithoutBlamingTheNonFatalGap()
    {
        var (result, after, before, _) = Execute(new CoverSpec
        {
            ReportDeclarations = ImmutableArray.Create("unrelated"),
        });

        Assert.False(result.Success);
        Assert.Contains("resolves to 0 report declarations", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("coverage-receipt-mismatch", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("target-declaration-missing", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsDeclarationProvedOnlyWithSorry()
    {
        var execution = Execute(new CoverSpec
        {
            TargetAxioms = ImmutableArray.Create("sorryAx"),
        });

        Assert.False(execution.Result.Success);
        Assert.Contains("lean-state-open", execution.Result.Error, StringComparison.Ordinal);
        AssertFailedDispositionDoesNotAdmitCoverage(execution);
    }

    [Fact]
    public void CoverRejectsMissingProducerEmissionAsPartialClosed()
    {
        var (result, after, before, _) = Execute(new CoverSpec { VerifyScribe = false });

        Assert.False(result.Success);
        Assert.Contains("scribe-emission-missing", result.Error, StringComparison.Ordinal);
        Assert.Contains("partial-closed", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsAtomWhoseContentAddressedReceiptDrifted()
    {
        // The atom's durable CAS blob is absent, so its fingerprint cannot be reproduced:
        // cover fails closed rather than binding a declaration to an unverifiable source atom.
        var (result, after, before, _) = Execute(
            new CoverSpec { IncludeCasBlob = false }, changes: RawChangeSet.Create(["README.md"]));

        Assert.False(result.Success);
        Assert.Contains("CAS blob is missing", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsAbsorbedTailThatIsNotClosed()
    {
        // A declaration proven with a non-standard (unregistered) axiom derives a
        // Tail truth state. Even when the residual atom already carries a verified
        // tail authorization — so it would reach Absorbed-Tail-deletable — cover
        // must reject: spec §3.4 ③ requires TruthDag=Closed with no
        // sorry/private/unregistered axiom.
        var execution = Execute(new CoverSpec
        {
            TargetAxioms = ImmutableArray.Create("customAxiom"),
            TailAuthorized = true,
        });

        Assert.False(execution.Result.Success);
        Assert.Contains("Closed", execution.Result.Error, StringComparison.Ordinal);
        Assert.Contains("absorbed-tail", execution.Result.Error, StringComparison.Ordinal);
        AssertFailedDispositionDoesNotAdmitCoverage(execution);
    }

    [Fact]
    public void CoverAbortsWhenLedgerChangedUnderItBetweenReadAndWrite()
    {
        // Compare-and-swap: the on-disk ledger no longer matches the bytes cover
        // validated against (a concurrent cover deposited in between). cover must
        // abort rather than silently overwrite the other deposit (lost update).
        var inputs = CoverWorld.Materialize(new CoverSpec());
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        var baselineFiles = DirectoryLedgerTestSupport.Project(inputs.Baseline);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var atomPath = currentFiles.Keys.Single(path =>
            path.EndsWith($"/{CoverWorld.DefaultAtomId}.yaml", StringComparison.Ordinal));
        var outputPath = Path.Combine(temporary.Path, atomPath.Replace('/', Path.DirectorySeparatorChar));
        var concurrent = currentFiles[atomPath] + "# concurrent deposit\n";
        File.WriteAllText(outputPath, concurrent, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(currentFiles),
                CoverWorld.Raw(baselineFiles)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions),
            CoverWorld.TimeProvider);
        var result = environment.CoverAtom(
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);

        Assert.False(result.Success);
        Assert.Contains("changed under us", result.Error, StringComparison.Ordinal);
        Assert.Equal(concurrent, File.ReadAllText(outputPath));
    }

    [Fact]
    public void CoverAbortsWhenLedgerDeletedBetweenReadAndWrite()
    {
        // Fail-closed: if the on-disk ledger disappeared between read and write
        // (e.g. deleted by another actor), cover must abort — not create a fresh
        // ledger and overwrite the missing deposit (no-silent-failure, first
        // principle). The gateway still holds the ledger cover validated against.
        var inputs = CoverWorld.Materialize(new CoverSpec());
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        var baselineFiles = DirectoryLedgerTestSupport.Project(inputs.Baseline);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var atomPath = currentFiles.Keys.Single(path =>
            path.EndsWith($"/{CoverWorld.DefaultAtomId}.yaml", StringComparison.Ordinal));
        var outputPath = Path.Combine(temporary.Path, atomPath.Replace('/', Path.DirectorySeparatorChar));
        File.Delete(outputPath);
        Assert.False(File.Exists(outputPath));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(currentFiles),
                CoverWorld.Raw(baselineFiles)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions),
            CoverWorld.TimeProvider);

        var result = environment.CoverAtom(
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);

        Assert.False(result.Success);
        Assert.Contains("missing", result.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(outputPath));
    }

    [Fact]
    public void CoverRejectsIncompleteArguments()
    {
        var spec = new CoverSpec();
        var (result, after, before, _) = Execute(spec, ["--cover-atom", spec.AtomId]);

        Assert.False(result.Success);
        Assert.Contains("USAGE: StrataLint cover-atom", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsRepeatedGidWithinOneEntryUpdate()
    {
        var spec = new CoverSpec();
        var inputs = spec.Materialize();

        var (result, after, before, _) = Execute(
            spec,
            ["--cover-atom", spec.AtomId,
                "--gid", inputs.Gid,
                "--gid", inputs.Gid,
                "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);

        Assert.False(result.Success);
        Assert.Contains("USAGE: StrataLint cover-atom", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverIsUnavailableWithoutScribeVerifier()
    {
        var inputs = new CoverSpec().Materialize();
        using var temporary = new TemporaryDirectory();
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(inputs.Files),
                CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report));

        var result = environment.CoverAtom(
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("Scribe emission verifier is unavailable", result.Error, StringComparison.Ordinal);
    }

    private static CoverExecution Execute(CoverSpec spec,
        IReadOnlyList<string>? args = null,
        RawChangeSet? changes = null)
    {
        var inputs = spec.Materialize();
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        var baselineFiles = DirectoryLedgerTestSupport.Project(inputs.Baseline);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var before = DirectoryLedgerTestSupport.Image(
            BackfillInventoryLoader.LoadRoot(temporary.Path));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                changes ?? RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(currentFiles),
                CoverWorld.Raw(baselineFiles)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions),
            CoverWorld.TimeProvider);
        var effectiveArgs = args
            ?? ["--cover-atom", spec.AtomId, "--gid", inputs.Gid, "--base", "baseline",
                "--envelope", inputs.EnvelopePath];
        var result = environment.CoverAtom(effectiveArgs);

        var afterDocument = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var after = DirectoryLedgerTestSupport.Image(afterDocument);
        return new CoverExecution(result, after, before, afterDocument);
    }

    private static string ExpectedAlignedScribeImage(
        CoverInputs inputs,
        ScribeEmissionRecord verifiedRecord)
    {
        var sources = inputs.Document.RequireDigestionSources()
            .Select(source => source with
            {
                Entries = source.Entries.Select(entry => entry with
                {
                    Receipts = entry.Receipts with
                    {
                        Scribe = entry.Receipts.Scribe.Select(receipt =>
                            entry.AtomId == CoverWorld.DefaultAtomId
                                && receipt.Gid == inputs.Gid
                                ? receipt with
                                {
                                    DefinitionSha256 = verifiedRecord.DefinitionSha256,
                                    EmissionSha256 = verifiedRecord.EmissionSha256,
                                }
                                : receipt).ToImmutableArray(),
                    },
                }).ToImmutableArray(),
            })
            .ToImmutableArray();
        return DirectoryLedgerTestSupport.Image(inputs.Document.WithDigestionSources(sources));
    }
}

internal sealed record CoverInputs(
    Dictionary<string, string> Files,
    Dictionary<string, string> Baseline,
    LeanAxiomReport Report,
    VerifiedScribeEmissions? VerifiedEmissions,
    string Gid,
    string EnvelopePath,
    string Ledger,
    BackfillInventoryDocument Document);

internal sealed record CoverUnrelatedSiblingSpec(
    string AtomId,
    ImmutableArray<string> CurrentCoverage,
    ImmutableArray<string> BaselineCoverage,
    ImmutableArray<string> UnresolvedSubitems);

// Declarative fixture for the cover gate matrix. Defaults produce a clean happy
// path (an open, CAS-backed residual atom whose target declaration is proven
// closed and Scribe-emitted); each gate test flips exactly one field.
internal sealed partial record CoverSpec
{
    internal string AtomId { get; init; } = CoverWorld.DefaultAtomId;

    internal string ModuleGid { get; init; } = "D5/S0/Carrier/Probe";

    internal string? Declaration { get; init; } = "probe";

    internal ImmutableArray<string> InitialCoverage { get; init; } = ImmutableArray<string>.Empty;

    internal string? InitialDefinitionSha256 { get; init; }

    internal string? InitialEmissionSha256 { get; init; }

    internal string Migration { get; init; } = "residual";

    internal string Truth { get; init; } = "open";

    internal ImmutableArray<string> InitialUnresolvedSubitems { get; init; } = [];

    internal bool IncludeCasBlob { get; init; } = true;

    internal ImmutableArray<string> ReportDeclarations { get; init; } = ImmutableArray.Create("probe");

    // Deposited declaration signature (kind/type) in the raw Lean report. The
    // pre-committed receipt signature defaults to match these, so the happy path
    // is a signature match; a gate test flips one side to force a mismatch.
    internal string ReportKind { get; init; } = "theorem";

    internal string ReportType { get; init; } = "True";

    internal ImmutableArray<string> TargetAxioms { get; init; } = ImmutableArray<string>.Empty;
    internal bool VerifyScribe { get; init; } = true;
    // Pre-committed formalization receipt (digestion-formalization-v1, spec §11.21).
    // Defaults produce a receipt that binds this atom and pins a signature equal to
    // the deposited declaration; each envelope gate test flips exactly one field.
    internal bool IncludeEnvelope { get; init; } = true;

    // Base-owned receipt (§11.21 hardening): in the honest two-phase deposit the
    // receipt is committed in PR-1 and is therefore part of the baseline at PR-2.
    // Default true keeps the receipt pre-committed in the baseline. Setting it
    // false models a same-PR (spec A16 hostile-fork) attack where the receipt is
    // fabricated in the candidate only and never pre-committed to the baseline.
    internal bool EnvelopeInBaseline { get; init; } = true;

    // When set, the baseline receipt pins this (divergent) signature while the
    // candidate copy of the receipt pins PrecommittedSignature/default. Models a
    // same-PR statement swap where the attacker co-tampers the candidate receipt
    // to match the swapped declaration: base-owned load must read the baseline
    // receipt and reject the swap.
    internal DigestionFormalizationSignature? BaselinePrecommittedSignature { get; init; }

    internal bool MalformedEnvelope { get; init; }
    internal bool NoncanonicalBaselineEnvelope { get; init; }
    internal string? EnvelopeAtomId { get; init; }

    internal string? EnvelopePrimaryGid { get; init; }

    internal DigestionFormalizationSignature? PrecommittedSignature { get; init; }

    internal string? EnvelopeCasRef { get; init; }

    internal string? EnvelopeRawSha256 { get; init; }

    internal string? BaselineCoverageGid { get; init; }

    internal (string AtomId, string Gid)? OtherAtomBinding { get; init; }

    // When true the residual entry carries a verified tail authorization, so a
    // target proven only with a non-standard axiom (Tail) derives an
    // absorbed-tail deletable state. Used to prove gate (6) rejects Tail.
    internal bool TailAuthorized { get; init; }

    // When true the baseline holds the covered declaration's Lean file with
    // identical bytes (the declaration is not new). Default: the file is new
    // relative to the baseline (absent), which is the ordinary cover case.
    internal bool BaselineTargetIdentical { get; init; }

    internal (string ModuleGid, string Declaration)? SecondaryTarget { get; init; }

    internal bool IncludeSecondaryPrecommittedSignature { get; init; } = true;

    internal DigestionFormalizationSignature? SecondaryPrecommittedSignature { get; init; }

    internal ImmutableArray<DigestionFormalizationExtension> AdditionalHostedExtensions { get; init; } = [];

    internal CoverUnrelatedSiblingSpec? UnrelatedSibling { get; init; }

    internal string Gid => Declaration is null ? ModuleGid : ModuleGid + "." + Declaration;

    internal CoverInputs Materialize() => CoverWorld.Materialize(this);
}

internal static partial class CoverWorld
{
    internal const string DefaultAtomId = "cover-1";
    internal static readonly DateTimeOffset RecordedAtUtc = new(2026, 8, 26, 4, 3, 2, TestBudgets.ZeroDuration);
    internal static TimeProvider TimeProvider { get; } = new FixedTimeProvider(RecordedAtUtc);

    internal static CoverSpec StaleReceiptSpec() => new()
    {
        InitialCoverage = ImmutableArray.Create("D5/S0/Carrier/Probe.probe"),
        InitialDefinitionSha256 = "sha256:" + new string('a', 64),
        InitialEmissionSha256 = "sha256:" + new string('b', 64),
        Migration = "absorbed",
        Truth = "closed",
    };

    internal static string[] AlignArgs(CoverInputs inputs) =>
        ["--atom-id", DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline"];

    internal static ProductionCliEnvironment Environment(
        string repositoryRoot,
        CoverInputs inputs,
        IReadOnlyDictionary<string, string> currentFiles) =>
        new(
            repositoryRoot,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Raw(currentFiles),
                Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions),
            TimeProvider);

    internal static RawRepositorySnapshot Raw(IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));

    internal static CoverInputs Materialize(CoverSpec spec)
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。cover fixture atom body。\n");
        var atom = Assert.Single(
            AtomizerRegistry.Atomize(SyntheticNumberedAtomizer.Id, sourceBytes, DigestionTestSupport.Rules).Claims);
        const string unrelatedSourcePath = "docs/CONTRIBUTING.md";
        var unrelatedSourceBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。unrelated sibling atom body。\n");
        var unrelatedAtom = spec.UnrelatedSibling is null
            ? null
            : Assert.Single(AtomizerRegistry.Atomize(
                SyntheticNumberedAtomizer.Id,
                unrelatedSourceBytes,
                DigestionTestSupport.Rules).Claims);
        var targetPath = spec.ModuleGid + ".lean";
        var targetBytes = Encoding.UTF8.GetBytes(DigestionTestSupport.Lean(spec.ModuleGid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var record = new ScribeEmissionRecord(
            spec.ModuleGid,
            ScribeEmissionAttestation.DefinitionPath(spec.ModuleGid),
            DigestionFingerprint.Compute(definition).RawSha256,
            ScribeEmissionAttestation.EmissionPath(spec.ModuleGid),
            DigestionFingerprint.Compute(emission).RawSha256);
        var records = MaterializeScribeRecords(spec, record);
        var attestation = ScribeEmissionAttestation.Write(records);

        string? tailAuthPath = null;
        string? tailAuthSha = null;
        var tailAuthBytes = ImmutableArray<byte>.Empty;
        if (spec.TailAuthorized)
        {
            tailAuthBytes = TailAuthorizationArtifact.Write(spec.AtomId, [spec.Gid]);
            tailAuthPath = TailAuthorizationArtifact.PathFor(spec.AtomId);
            tailAuthSha = DigestionFingerprint.Compute(tailAuthBytes.AsSpan()).RawSha256;
        }

        var document = BuildLedger(
            spec,
            atom,
            spec.InitialCoverage,
            includeOtherAtom: true,
            tailAuthPath,
            tailAuthSha,
            gid => FrozenStatementIdFor(spec, gid),
            unrelatedAtom,
            unrelatedSourcePath,
            useUnrelatedBaselineCoverage: false);
        var ledger = DirectoryLedgerTestSupport.Image(document);
        var envelopePath = "Meta/Digestion/formalizations/" + spec.AtomId + ".v1.json";
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Meta/registry.yaml"] = TestRegistry.Canonical,
            ["Meta/domains.yaml"] = TestRegistry.Domains,
            [RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes),
            [targetPath] = Encoding.UTF8.GetString(targetBytes),
            [ScribeEmissionAttestation.DefinitionPath(spec.ModuleGid)] = Encoding.UTF8.GetString(definition),
            [ScribeEmissionAttestation.EmissionPath(spec.ModuleGid)] = Encoding.UTF8.GetString(emission),
            [ScribeEmissionAttestation.RelativePath] = Encoding.UTF8.GetString(attestation.AsSpan()),
        };
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        if (unrelatedAtom is not null)
        {
            files[unrelatedSourcePath] = Encoding.UTF8.GetString(unrelatedSourceBytes);
            var (unrelatedCasPath, unrelatedCasBytes) = DigestionTestSupport.CasFile(unrelatedAtom);
            files[unrelatedCasPath] = Encoding.UTF8.GetString(unrelatedCasBytes);
        }
        MaterializeSecondaryFiles(spec, files);
        if (spec.IncludeEnvelope)
        {
            files[envelopePath] = Encoding.UTF8.GetString(Envelope(spec, atom).AsSpan());
        }
        MaterializeOtherAtomFormalizationReceipt(spec, atom, files);
        if (spec.IncludeCasBlob)
        {
            var (casPath, casBytes) = DigestionTestSupport.CasFile(atom);
            files[casPath] = Encoding.UTF8.GetString(casBytes);
        }

        if (tailAuthPath is not null)
        {
            files[tailAuthPath] = Encoding.UTF8.GetString(tailAuthBytes.AsSpan());
        }

        var baselineCoverage = spec.BaselineCoverageGid is not null
            ? ImmutableArray.Create(spec.BaselineCoverageGid)
            : spec.InitialCoverage;
        var baselineDocument = BuildLedger(
            spec,
            atom,
            baselineCoverage,
            includeOtherAtom: false,
            null,
            null,
            unrelatedAtom: unrelatedAtom,
            unrelatedSourcePath: unrelatedSourcePath,
            useUnrelatedBaselineCoverage: true);
        var baseline = new Dictionary<string, string>(files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(baseline, baselineDocument);

        // File-level declaration newness (gate ②c): by default the covered Lean
        // file is new relative to the baseline (absent). BaselineTargetIdentical
        // keeps it byte-identical at base so the declaration reads as not-new.
        if (!spec.BaselineTargetIdentical)
        {
            baseline.Remove(targetPath);
        }

        // Base-owned receipt (§11.21 hardening): the receipt is authoritative only
        // when it is pre-committed to the baseline. A same-PR attack fabricates the
        // receipt in the candidate only (EnvelopeInBaseline=false) — drop it from
        // the baseline so the base-owned load sees no pre-commitment.
        if (spec.IncludeEnvelope && !spec.EnvelopeInBaseline)
        {
            baseline.Remove(envelopePath);
        }

        // Co-tampered same-PR swap: the baseline holds the honest receipt while the
        // candidate copy is overwritten to match a swapped declaration. Only the
        // baseline receipt is authoritative under base-owned load.
        if (spec.IncludeEnvelope && spec.EnvelopeInBaseline && spec.BaselinePrecommittedSignature is not null)
        {
            baseline[envelopePath] = Encoding.UTF8.GetString(
                Envelope(spec with { PrecommittedSignature = spec.BaselinePrecommittedSignature }, atom).AsSpan());
        }

        if (spec.IncludeEnvelope && spec.EnvelopeInBaseline && spec.NoncanonicalBaselineEnvelope)
        {
            baseline[envelopePath] = baseline[envelopePath].Replace("\": ", "\":", StringComparison.Ordinal);
        }

        var declarations = spec.ReportDeclarations
            .Select(name => new LeanDeclaration(name, spec.ReportKind, spec.ReportType, spec.TargetAxioms))
            .ToImmutableArray();
        var report = MaterializeReport(spec, targetPath, declarations);

        MaterializeFrozenLedger(spec, report, targetPath, files, baseline);

        var verified = spec.VerifyScribe
            ? VerifiedScribeEmissions.Create(records, MaterializeVerifiedGids(spec))
            : VerifiedScribeEmissions.Empty;

        return new CoverInputs(
            files,
            baseline,
            report,
            verified,
            spec.Gid,
            envelopePath,
            ledger,
            document);
    }

    // Build the pre-committed digestion-formalization-v1 receipt bytes. Defaults
    // bind this atom (atom_id + content fingerprint) and pin a signature equal to
    // the deposited declaration; MalformedEnvelope writes non-receipt bytes so the
    // fail-closed loader is exercised.
    private static ImmutableArray<byte> Envelope(CoverSpec spec, DigestionAtom atom)
    {
        if (spec.MalformedEnvelope)
        {
            return ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("{ not a receipt"));
        }

        var declarationName = spec.Declaration ?? "probe";
        var primaryGid = spec.EnvelopePrimaryGid
            ?? (spec.Declaration is null ? spec.ModuleGid + ".probe" : spec.Gid);
        var signature = spec.PrecommittedSignature
            ?? new DigestionFormalizationSignature(declarationName, spec.ReportKind, spec.ReportType);
        return DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            spec.EnvelopeAtomId ?? spec.AtomId,
            primaryGid,
            signature,
            spec.EnvelopeCasRef ?? atom.Fingerprints.RawSha256,
            spec.EnvelopeRawSha256 ?? atom.Fingerprints.RawSha256,
            HostedExtensions(spec, primaryGid)));
    }

    private static ImmutableArray<DigestionFormalizationExtension> HostedExtensions(
        CoverSpec spec,
        string primaryGid)
    {
        var extensions = spec.AdditionalHostedExtensions
            .Where(extension => !string.Equals(extension.Gid, primaryGid, StringComparison.Ordinal))
            .ToList();
        if (spec.IncludeSecondaryPrecommittedSignature
            && spec.SecondaryTarget is { } secondary)
        {
            var extension = new DigestionFormalizationExtension(
                secondary.ModuleGid + "." + secondary.Declaration,
                spec.SecondaryPrecommittedSignature
                    ?? new DigestionFormalizationSignature(
                        secondary.Declaration,
                        spec.ReportKind,
                        spec.ReportType));
            if (!string.Equals(extension.Gid, primaryGid, StringComparison.Ordinal))
            {
                extensions.Add(extension);
            }
        }

        return extensions
            .OrderBy(static extension => extension.Gid, StringComparer.Ordinal)
            .ToImmutableArray();
    }
}

internal sealed class FixedTimeProvider(DateTimeOffset utcNow) : TimeProvider { public override DateTimeOffset GetUtcNow() => utcNow; }
