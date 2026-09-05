using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// Phase 1 cover transaction gate matrix. cover binds one already-proven Lean
// declaration to an existing open residual atom by writing a coverage edge plus
// its Scribe receipt, all-or-nothing. Precondition and integrity rejects
// leave the ledger unchanged; a terminal initial-cover failure writes only its
// disposition.
public sealed partial class CoverAtomTests
{
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
        Assert.Single(entry.Coverage);
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
        var (result, after, before, _) = Execute(
            spec,
            ["--cover-atom", "no-such-atom", "--gid", spec.Gid, "--base", "baseline"]);

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
        Assert.Single(entry.Coverage);
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
        Assert.Equal(
            "COVER_INVALID current edge GID D5/S0/Carrier/Probe.probe has no unique active "
                + "frozen statement: coverage GID resolves to 0 current report declarations: "
                + "D5/S0/Carrier/Probe.probe\n",
            result.Error);
        Assert.DoesNotContain("coverage-target-mismatch", result.Error, StringComparison.Ordinal);
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
        Assert.Equal(execution.Before, execution.After);
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
        Assert.Contains("lean-state-tail", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(execution.Before, execution.After);
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
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline"]);

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
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline"]);

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
                "--base", "baseline"]);

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
        RawChangeSet? changes = null,
        LeanAxiomReport? currentReport = null)
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
            new FakeLeanReportSource(currentReport ?? inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions),
            CoverWorld.TimeProvider);
        var effectiveArgs = args
            ?? ["--cover-atom", spec.AtomId, "--gid", inputs.Gid, "--base", "baseline"];
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
