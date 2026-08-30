using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void AdmissionAllowsUnregisteredGenreWhenProjectionMatches()
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

        Assert.Empty(result.Findings);
    }

    [Fact]
    public void AdmissionRejectsPseudoemptyUnregisteredGenreProjection()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**猜想 3.6(未登记标题)[证]。**unknown。\n");
        var atomized = ConeAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var migration = CoarseMigration(sourceBytes, sourceBytes, atomized);
        var candidate = WithGenreCheck(migration.Candidate, GenreRegistryCheck.Collected([]));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            baselineSnapshot: migration.BaselineSnapshot);

        Assert.Contains(result.Findings, finding =>
            finding.Contains("genre registry projection differs", StringComparison.Ordinal)
            && finding.Contains("stored collected []", StringComparison.Ordinal)
            && finding.Contains("recomputed collected [猜想]", StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsMissingUnregisteredGenreToken()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**猜想 3.1(未登记标题)[证]。**一。\n\n"
            + "**假说 3.2(未登记标题)[证]。**二。\n");
        var atomized = ConeAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var migration = CoarseMigration(sourceBytes, sourceBytes, atomized);
        var candidate = WithGenreCheck(
            migration.Candidate,
            GenreRegistryCheck.Collected(["假说"]));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            baselineSnapshot: migration.BaselineSnapshot);

        Assert.Contains(result.Findings, finding =>
            finding.Contains("genre registry projection differs", StringComparison.Ordinal)
            && finding.Contains("recomputed collected [假说, 猜想]", StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsExtraUnregisteredGenreToken()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**猜想 3.1(未登记标题)[证]。**一。\n");
        var atomized = ConeAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var migration = CoarseMigration(sourceBytes, sourceBytes, atomized);
        var candidate = WithGenreCheck(
            migration.Candidate,
            GenreRegistryCheck.Collected(["假说", "猜想"]));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            baselineSnapshot: migration.BaselineSnapshot);

        Assert.Contains(result.Findings, finding =>
            finding.Contains("genre registry projection differs", StringComparison.Ordinal)
            && finding.Contains("stored collected [假说, 猜想]", StringComparison.Ordinal)
            && finding.Contains("recomputed collected [猜想]", StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsGenreRegistryStateMismatch()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**引理 3.1(已登记标题)[证]。**一。\n");
        var atomized = ConeAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var migration = CoarseMigration(sourceBytes, sourceBytes, atomized);
        var candidate = WithGenreCheck(migration.Candidate, GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            baselineSnapshot: migration.BaselineSnapshot);

        Assert.Contains(result.Findings, finding =>
            finding.Contains("genre registry projection differs", StringComparison.Ordinal)
            && finding.Contains("stored no-registry []", StringComparison.Ordinal)
            && finding.Contains("recomputed collected []", StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsNoRegistryMarkerForRegisteredEmptySource()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# Empty registered source\n");
        var atomized = new AtomizedTheoryDocument(
            [],
            [new DigestionSlice(false, ImmutableArray.CreateRange(sourceBytes))],
            GenreRegistryCheck.Collected([]));
        var migration = CoarseMigration(
            Encoding.UTF8.GetBytes("old"),
            sourceBytes);
        var candidate = WithGenreCheck(
            migration.Candidate,
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized,
            migration.BaselineSnapshot);

        Assert.Contains(result.Findings, finding =>
            finding.Contains("genre registry projection differs", StringComparison.Ordinal)
            && finding.Contains("stored no-registry []", StringComparison.Ordinal)
            && finding.Contains("recomputed collected []", StringComparison.Ordinal));
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
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(AtomId(migration.Coarse)));
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(AtomId(atomized.Claims[0])));
    }

    [Fact]
    public void AdmissionRechecksAndAllowsMatchingOpenProjectionWhenCodeClosureChanges()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n**未登记体 2.1**。claim。\n");
        var atomized = PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var atom = Assert.Single(atomized.Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var ledger = WithGenreCheck(
            WithAtomizer(
                Ledger([], CasEntry("inherited-receipt", atom, captured.Reference)),
                AtomizerRegistry.PzgId),
            atomized.GenreRegistryCheck);
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
        Assert.Empty(result.Findings);
    }

    [Fact]
    public void AdmissionDoesNotReatomizeForAnUnrelatedRepositoryChange()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n**未登记体 2.1**。claim。\n");
        var atomized = PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var atom = Assert.Single(atomized.Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var ledger = WithGenreCheck(
            WithAtomizer(
                Ledger([], CasEntry("inherited-receipt", atom, captured.Reference)),
                AtomizerRegistry.PzgId),
            atomized.GenreRegistryCheck);
        var baselineSnapshot = DigestionTestSupport.Snapshot(
            ("docs/source.md", sourceBytes),
            (captured.RelativePath, captured.Bytes.ToArray()),
            (TheoryAtomizerDataLoader.DataPath, DigestionTestSupport.RulesBytes.ToArray()),
            ("tools/StrataLint.Engine/Digestion/Atomizers/PzgAtomizer.cs", Encoding.UTF8.GetBytes("same")),
            ("Meta/domains.yaml", Encoding.UTF8.GetBytes("old")));
        var candidateSnapshot = DigestionTestSupport.Snapshot(
            ("docs/source.md", sourceBytes),
            (captured.RelativePath, captured.Bytes.ToArray()),
            (TheoryAtomizerDataLoader.DataPath, DigestionTestSupport.RulesBytes.ToArray()),
            ("tools/StrataLint.Engine/Digestion/Atomizers/PzgAtomizer.cs", Encoding.UTF8.GetBytes("same")),
            ("Meta/domains.yaml", Encoding.UTF8.GetBytes("new")));
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

        Assert.Equal(0, calls);
        Assert.Empty(result.Findings);
    }

    [Theory]
    [InlineData("Directory.Packages.props")]
    [InlineData("tools/StrataLint.Engine/StrataLint.Engine.csproj")]
    public void AdmissionRechecksWhenAtomizerBuildInputChanges(string changedPath)
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n**未登记体 2.1**。claim。\n");
        var atomized = PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var atom = Assert.Single(atomized.Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var ledger = WithGenreCheck(
            WithAtomizer(
                Ledger([], CasEntry("inherited-receipt", atom, captured.Reference)),
                AtomizerRegistry.PzgId),
            atomized.GenreRegistryCheck);
        var baselineSnapshot = DigestionTestSupport.Snapshot(
            ("docs/source.md", sourceBytes),
            (captured.RelativePath, captured.Bytes.ToArray()),
            (changedPath, Encoding.UTF8.GetBytes("old")));
        var candidateSnapshot = DigestionTestSupport.Snapshot(
            ("docs/source.md", sourceBytes),
            (captured.RelativePath, captured.Bytes.ToArray()),
            (changedPath, Encoding.UTF8.GetBytes("new")));
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
        Assert.Empty(result.Findings);
    }

    [Fact]
    public void AdmissionGenreProbeDefersToAtomizerIntegrityFinding()
    {
        var baselineBytes = Encoding.UTF8.GetBytes("old");
        var candidateBytes = ImmutableArray.Create((byte)'a');
        var corrupt = new DigestionAtom(
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
            ["source source atomizer integrity failed: claim at byte 0 fingerprint does not match its raw bytes"],
            result.Findings.ToArray());
    }

    [Fact]
    public void AdmissionGenreProbeAllowsDistinctContentWithoutPathDisambiguation()
    {
        var baselineBytes = Encoding.UTF8.GetBytes("old");
        var firstBytes = ImmutableArray.Create((byte)'a');
        var secondBytes = ImmutableArray.Create((byte)'b');
        var first = new DigestionAtom(
            0,
            1,
            firstBytes,
            DigestionFingerprint.Compute(firstBytes.AsSpan()),
            []);
        var second = new DigestionAtom(
            1,
            2,
            secondBytes,
            DigestionFingerprint.Compute(secondBytes.AsSpan()),
            []);
        var atomized = new AtomizedTheoryDocument(
            [first, second],
            [new DigestionSlice(true, firstBytes), new DigestionSlice(true, secondBytes)],
            GenreRegistryCheck.Collected([]));
        var migration = CoarseMigration(baselineBytes, [(byte)'a', (byte)'b']);
        var candidate = WithGenreCheck(migration.Candidate, atomized.GenreRegistryCheck);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            migration.CandidateSnapshot,
            migration.Baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized,
            migration.BaselineSnapshot);

        Assert.Empty(result.Findings);
        Assert.Equal(
            [
                first.Fingerprints.RawSha256["sha256:".Length..],
                second.Fingerprints.RawSha256["sha256:".Length..],
            ],
            result.Residual.Select(static item => item.SuggestedAtomId));
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
            0,
            baselineBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var coarseCapture = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var baseline = WithAtomizer(
            Ledger([], CasEntry("coarse-receipt", coarse, coarseCapture.Reference)),
            AtomizerRegistry.NoAtomizerId);
        var entries = new List<DigestionLedgerEntry>
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

        var candidate = WithAtomizer(
            Ledger([], entries.ToArray()),
            AtomizerRegistry.ConeId);
        if (candidateAtomized is not null)
        {
            candidate = WithGenreCheck(candidate, candidateAtomized.GenreRegistryCheck);
        }
        return new CoarseMigrationFixture(
            baseline,
            candidate,
            Snapshot(baselineBytes, [coarseCapture]),
            Snapshot(candidateBytes, captures),
            coarse);
    }

    private static BackfillInventoryDocument WithGenreCheck(
        BackfillInventoryDocument document,
        GenreRegistryCheck check) =>
        document.WithDigestionSources(document.RequireDigestionSources()
            .Select(source => source with
            {
                GenreRegistryProjection = GenreRegistryProjection.Available(check),
            })
            .ToImmutableArray());

    private sealed record CoarseMigrationFixture(
        BackfillInventoryDocument Baseline,
        BackfillInventoryDocument Candidate,
        RepositorySnapshot BaselineSnapshot,
        RepositorySnapshot CandidateSnapshot,
        DigestionAtom Coarse);
}
