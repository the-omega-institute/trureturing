using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void AdmissionRejectsUnregisteredGenreWhenAtomizerChangesBehindIdenticalDataInputs()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**猜想 3.6(未登记标题)[证]。**unknown。\n");
        var atomized = ConeAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var migration = CoarseMigration(sourceBytes, sourceBytes, atomized);

        var result = DigestionLedgerAligner.Evaluate(
            migration.Candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            baselineSnapshot: migration.BaselineSnapshot);

        Assert.Contains(
            $"source source uses claim genres its dialect does not register: 猜想. "
            + $"Register them in {TheoryAtomizerDataLoader.DataPath} or correct the volume.",
            result.Findings);
    }

    [Fact]
    public void AdmissionAllowsRegisteredGenreWhenAtomizerChangesBehindIdenticalDataInputs()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**引理 3.5(已登记标题)[证]。**known。\n");
        var atomized = ConeAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var migration = CoarseMigration(sourceBytes, sourceBytes, atomized);

        var result = DigestionLedgerAligner.Evaluate(
            migration.Candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            baselineSnapshot: migration.BaselineSnapshot);

        Assert.Empty(result.Findings);
        Assert.Empty(result.Residual);
        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            result.AlignmentFor("coarse-receipt"));
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor("fine-receipt-0"));
    }

    [Fact]
    public void AdmissionRechecksGenreWhenRepositoryCodeClosureChangesBehindIdenticalDataInputs()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n**未登记体 2.1**。claim。\n");
        var atomized = PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var atom = Assert.Single(atomized.Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(
            Ledger([], CasEntry("inherited-receipt", atom, captured.Reference))
                .Replace(
                    $"atomizer: {AtomizerRegistry.GictId}",
                    $"atomizer: {AtomizerRegistry.PzgId}",
                    StringComparison.Ordinal));
        var baselineSnapshot = DigestionTestSupport.Snapshot(
            ("docs/source.md", sourceBytes),
            (captured.RelativePath, captured.Bytes.ToArray()),
            ("tools/StrataLint.Engine/Digestion/Atomizers/PzgAtomizer.cs", Encoding.UTF8.GetBytes("old")));
        var candidateSnapshot = DigestionTestSupport.Snapshot(
            ("docs/source.md", sourceBytes),
            (captured.RelativePath, captured.Bytes.ToArray()),
            ("tools/StrataLint.Engine/Digestion/Atomizers/PzgAtomizer.cs", Encoding.UTF8.GetBytes("new")));
        var calls = 0;

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            candidateSnapshot,
            ledger,
            DigestionAlignmentMode.Admission,
            _ => (_, _) =>
            {
                calls++;
                return atomized;
            },
            baselineSnapshot);

        Assert.Equal(1, calls);
        Assert.Contains(result.Findings, finding => finding.Contains(
            "uses claim genres its dialect does not register: 未登记体",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionGenreProbeDefersToAtomizerIntegrityFinding()
    {
        var baselineBytes = Encoding.UTF8.GetBytes("old");
        var candidateBytes = ImmutableArray.Create((byte)'a');
        var corrupt = new DigestionAtom(
            "theorem/1.1",
            0,
            1,
            candidateBytes,
            new DigestionFingerprints(
                "sha256:" + new string('0', 64),
                "sha256:" + new string('0', 64)),
            []);
        var atomized = new AtomizedTheoryDocument(
            [corrupt],
            [new DigestionSlice(true, candidateBytes)],
            GenreRegistryCheck.Collected(["未登记体"]));
        var migration = CoarseMigration(baselineBytes, candidateBytes.ToArray());

        var result = DigestionLedgerAligner.Evaluate(
            migration.Candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized,
            migration.BaselineSnapshot);

        Assert.Equal(
            ["source source atomizer integrity failed: claim theorem/1.1 fingerprint does not match its raw bytes"],
            result.Findings.ToArray());
    }

    [Fact]
    public void AdmissionGenreProbeDefersToDuplicateAstPathFinding()
    {
        var baselineBytes = Encoding.UTF8.GetBytes("old");
        var firstBytes = ImmutableArray.Create((byte)'a');
        var secondBytes = ImmutableArray.Create((byte)'b');
        var first = new DigestionAtom(
            "theorem/duplicate",
            0,
            1,
            firstBytes,
            DigestionFingerprint.Compute(firstBytes.AsSpan()),
            []);
        var second = new DigestionAtom(
            "theorem/duplicate",
            1,
            2,
            secondBytes,
            DigestionFingerprint.Compute(secondBytes.AsSpan()),
            []);
        var atomized = new AtomizedTheoryDocument(
            [first, second],
            [new DigestionSlice(true, firstBytes), new DigestionSlice(true, secondBytes)],
            GenreRegistryCheck.Collected(["未登记体"]));
        var migration = CoarseMigration(baselineBytes, [(byte)'a', (byte)'b']);

        var result = DigestionLedgerAligner.Evaluate(
            migration.Candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized,
            migration.BaselineSnapshot);

        Assert.Equal(
            ["source source duplicate atomized ast_path: theorem/duplicate"],
            result.Findings.ToArray());
    }

    [Fact]
    public void AdmissionGenreProbeDoesNotCatchAnUnownedAtomizerException()
    {
        var migration = CoarseMigration(
            Encoding.UTF8.GetBytes("old"),
            Encoding.UTF8.GetBytes("new"));
        var calls = 0;

        var exception = Assert.Throws<FormatException>(() => DigestionLedgerAligner.Evaluate(
            migration.Candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) =>
            {
                calls++;
                throw new FormatException("unknown declared dialect");
            },
            migration.BaselineSnapshot));

        Assert.Equal("unknown declared dialect", exception.Message);
        Assert.Equal(1, calls);
    }

    [Fact]
    public void IngestAbortsWhenCollectedGenresViolateTheirProgrammingContract()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();

        var exception = Assert.Throws<InvalidOperationException>(() => DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(Encoding.UTF8.GetBytes("source"), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => new AtomizedTheoryDocument(
                [],
                [],
                GenreRegistryCheck.Collected(default))));

        Assert.Equal("collected unregistered genres must be initialized", exception.Message);
    }

    private static CoarseMigrationFixture CoarseMigration(
        byte[] baselineBytes,
        byte[] candidateBytes,
        AtomizedTheoryDocument? candidateAtomized = null)
    {
        var coarseBytes = ImmutableArray.CreateRange(baselineBytes);
        var coarse = new DigestionAtom(
            "coarse/source",
            0,
            baselineBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var coarseCapture = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var baseline = BackfillInventoryLoader.Load(
            Ledger([], CasEntry("coarse-receipt", coarse, coarseCapture.Reference))
                .Replace(
                    $"atomizer: {AtomizerRegistry.GictId}",
                    $"atomizer: {AtomizerRegistry.NoAtomizerId}",
                    StringComparison.Ordinal));
        var entries = new List<string>
        {
            CasEntry("coarse-receipt", coarse, coarseCapture.Reference),
        };
        var captures = new List<DigestionCasObject> { coarseCapture };
        if (candidateAtomized is not null)
        {
            for (var index = 0; index < candidateAtomized.Claims.Length; index++)
            {
                var atom = candidateAtomized.Claims[index];
                var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
                entries.Add(CasEntry($"fine-receipt-{index}", atom, capture.Reference));
                captures.Add(capture);
            }
        }

        var candidate = BackfillInventoryLoader.Load(
            Ledger(["coarse-receipt"], entries.ToArray())
                .Replace(
                    $"atomizer: {AtomizerRegistry.GictId}",
                    $"atomizer: {AtomizerRegistry.ConeId}",
                    StringComparison.Ordinal));
        return new CoarseMigrationFixture(
            baseline,
            candidate,
            Snapshot(baselineBytes, [coarseCapture]),
            Snapshot(candidateBytes, captures));
    }

    private sealed record CoarseMigrationFixture(
        BackfillInventoryDocument Baseline,
        BackfillInventoryDocument Candidate,
        RepositorySnapshot BaselineSnapshot,
        RepositorySnapshot CandidateSnapshot);
}
