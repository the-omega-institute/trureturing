using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// Phase 1 cover transaction gate matrix. cover binds one already-proven Lean
// declaration to an existing open residual atom by writing coverage_gids +
// coverage/scribe receipts, all-or-nothing. Every reject path must leave
// Meta/BACKFILL.yaml byte-unchanged.
public sealed class CoverAtomTests
{
    [Fact]
    public void CoverBindsDeletableDeclarationAndWritesCoverageReceipts()
    {
        var (result, after, before) = Execute(new CoverSpec());

        Assert.True(result.Success, result.Error);
        Assert.Contains($"COVER atom_id={CoverWorld.DefaultAtomId}", result.Output, StringComparison.Ordinal);
        Assert.Contains("gid=D5/S0/Carrier/Probe.probe", result.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.NotEqual(before, after);

        var entry = Assert.Single(
            BackfillInventoryLoader.Load(after).RequireDigestionEntries(),
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
        var (result, after, before) = Execute(new CoverSpec
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
        var (result, after, before) = Execute(new CoverSpec
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
        var (result, after, before) = Execute(
            spec,
            ["--cover-atom", "no-such-atom", "--gid", spec.Gid, "--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("is absent", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsGidWithoutDeclarationSelector()
    {
        var (result, after, before) = Execute(new CoverSpec { Declaration = null });

        Assert.False(result.Success);
        Assert.Contains("must select a Lean declaration", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsGidAlreadyBoundInBaselineLedger()
    {
        var (result, after, before) = Execute(new CoverSpec
        {
            BaselineCoverageGid = "D5/S0/Carrier/Probe.probe",
        });

        Assert.False(result.Success);
        Assert.Contains("already bound in the baseline", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsGidAlreadyBoundToAnotherAtom()
    {
        var (result, after, before) = Execute(new CoverSpec
        {
            OtherAtomBinding = ("sibling-atom", "D5/S0/Carrier/Probe.probe"),
        });

        Assert.False(result.Success);
        Assert.Contains("already bound to atom sibling-atom", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsDeclarationAbsentFromLeanReport()
    {
        var (result, after, before) = Execute(new CoverSpec
        {
            ReportDeclarations = ImmutableArray.Create("unrelated"),
        });

        Assert.False(result.Success);
        Assert.Contains("target-declaration-missing", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsDeclarationProvedOnlyWithSorry()
    {
        var (result, after, before) = Execute(new CoverSpec
        {
            TargetAxioms = ImmutableArray.Create("sorryAx"),
        });

        Assert.False(result.Success);
        Assert.Contains("lean-state-open", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsUnverifiedScribeEmissionAsPartialClosed()
    {
        var (result, after, before) = Execute(new CoverSpec { VerifyScribe = false });

        Assert.False(result.Success);
        Assert.Contains("scribe-emission-unverified", result.Error, StringComparison.Ordinal);
        Assert.Contains("partial-closed", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsAtomWhoseContentAddressedReceiptDrifted()
    {
        // The atom's durable CAS blob is absent, so its content-addressed
        // fingerprint can no longer be reproduced: cover fails closed rather than
        // binding a declaration to an unverifiable source atom.
        var (result, after, before) = Execute(new CoverSpec { IncludeCasBlob = false });

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
        var (result, after, before) = Execute(new CoverSpec
        {
            TargetAxioms = ImmutableArray.Create("customAxiom"),
            TailAuthorized = true,
        });

        Assert.False(result.Success);
        Assert.Contains("Closed", result.Error, StringComparison.Ordinal);
        Assert.Contains("absorbed-tail", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsDeclarationWhoseLeanFileIsUnchangedFromBaseline()
    {
        // The covered declaration's Lean file is byte-identical at the baseline,
        // so the declaration is not new — an old theorem cannot be re-deposited as
        // a fresh atom (spec gate ②, "new relative to base").
        var (result, after, before) = Execute(new CoverSpec { BaselineTargetIdentical = true });

        Assert.False(result.Success);
        Assert.Contains("is not new", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverAbortsWhenLedgerChangedUnderItBetweenReadAndWrite()
    {
        // Compare-and-swap: the on-disk ledger no longer matches the bytes cover
        // validated against (a concurrent cover deposited in between). cover must
        // abort rather than silently overwrite the other deposit (lost update).
        var inputs = CoverWorld.Materialize(new CoverSpec());
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        var concurrent = inputs.Ledger + "\n# concurrent deposit\n";
        File.WriteAllText(outputPath, concurrent, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(inputs.Files),
                CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions));

        var result = environment.CoverAtom(
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("changed under us", result.Error, StringComparison.Ordinal);
        Assert.Equal(concurrent, File.ReadAllText(outputPath));
    }

    [Fact]
    public void CoverRejectsIncompleteArguments()
    {
        var spec = new CoverSpec();
        var (result, after, before) = Execute(spec, ["--cover-atom", spec.AtomId]);

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

    // §4 semantic-fidelity gates are Phase 2: they require upstream
    // digestion-formalization-v1 + digestion-fidelity-attestation-v1 receipts and
    // /sshx multi-model consensus on the fidelity contract, none of which exist yet.
    [Fact(Skip = "Phase 2 §4: needs upstream digestion-formalization-v1/"
        + "digestion-fidelity-attestation-v1 receipts + /sshx consensus")]
    public void CoverRejectsFormalizationWhoseSignatureDoesNotMatchPreCommittedClaim()
    {
    }

    [Fact(Skip = "Phase 2 §4: needs upstream digestion-formalization-v1/"
        + "digestion-fidelity-attestation-v1 receipts + /sshx consensus")]
    public void CoverRejectsHollowTrueEmissionThatDischargesNothing()
    {
    }

    private static (CommandResult Result, string After, string Before) Execute(
        CoverSpec spec,
        IReadOnlyList<string>? args = null)
    {
        var inputs = spec.Materialize();
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(inputs.Files),
                CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions));
        var effectiveArgs = args
            ?? ["--cover-atom", spec.AtomId, "--gid", inputs.Gid, "--base", "baseline"];

        var result = environment.CoverAtom(effectiveArgs);

        return (result, File.ReadAllText(outputPath), inputs.Ledger);
    }
}

internal sealed record CoverInputs(
    Dictionary<string, string> Files,
    Dictionary<string, string> Baseline,
    LeanAxiomReport Report,
    VerifiedScribeEmissions? VerifiedEmissions,
    string Gid,
    string Ledger);

// Declarative fixture for the cover gate matrix. Defaults produce a clean happy
// path (an open, CAS-backed residual atom whose target declaration is proven
// closed and Scribe-emitted); each gate test flips exactly one field.
internal sealed record CoverSpec
{
    internal string AtomId { get; init; } = CoverWorld.DefaultAtomId;

    internal string ModuleGid { get; init; } = "D5/S0/Carrier/Probe";

    internal string? Declaration { get; init; } = "probe";

    internal ImmutableArray<string> InitialCoverage { get; init; } = ImmutableArray<string>.Empty;

    internal string Migration { get; init; } = "residual";

    internal string Truth { get; init; } = "open";

    internal bool IncludeCasBlob { get; init; } = true;

    internal ImmutableArray<string> ReportDeclarations { get; init; } = ImmutableArray.Create("probe");

    internal ImmutableArray<string> TargetAxioms { get; init; } = ImmutableArray<string>.Empty;

    internal bool VerifyScribe { get; init; } = true;

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

    internal string Gid => Declaration is null ? ModuleGid : ModuleGid + "." + Declaration;

    internal CoverInputs Materialize() => CoverWorld.Materialize(this);
}

internal static class CoverWorld
{
    // Neutral atom id: the source atom is never re-atomized under admission-mode
    // alignment, so the fixture builds it directly and keeps program sources free
    // of internal theory-volume tokens (TheoryIsolationPolicy).
    internal const string DefaultAtomId = "cover-1";

    internal static RawRepositorySnapshot Raw(IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));

    internal static CoverInputs Materialize(CoverSpec spec)
    {
        var atomBytes = Encoding.UTF8.GetBytes("cover fixture atom body\n");
        var atom = new DigestionAtom(
            "claim/probe",
            0,
            atomBytes.Length,
            ImmutableArray.CreateRange(atomBytes),
            DigestionFingerprint.Compute(atomBytes),
            ImmutableArray<DigestionContext>.Empty);
        var sourceBytes = Encoding.UTF8.GetBytes("cover fixture governance source\n");
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
        var attestation = ScribeEmissionAttestation.Write([record]);

        string? tailAuthPath = null;
        string? tailAuthSha = null;
        var tailAuthBytes = ImmutableArray<byte>.Empty;
        if (spec.TailAuthorized)
        {
            tailAuthBytes = TailAuthorizationArtifact.Write(spec.AtomId, [spec.Gid]);
            tailAuthPath = TailAuthorizationArtifact.PathFor(spec.AtomId);
            tailAuthSha = DigestionFingerprint.Compute(tailAuthBytes.AsSpan()).RawSha256;
        }

        var ledger = BuildLedger(
            spec,
            atom,
            spec.InitialCoverage,
            includeOtherAtom: true,
            tailAuthPath,
            tailAuthSha);
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [BackfillInventoryLoader.RelativePath] = ledger,
            ["Meta/registry.yaml"] = TestRegistry.Canonical,
            ["Meta/domains.yaml"] = TestRegistry.Domains,
            [GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes),
            [targetPath] = Encoding.UTF8.GetString(targetBytes),
            [ScribeEmissionAttestation.DefinitionPath(spec.ModuleGid)] = Encoding.UTF8.GetString(definition),
            [ScribeEmissionAttestation.EmissionPath(spec.ModuleGid)] = Encoding.UTF8.GetString(emission),
            [ScribeEmissionAttestation.RelativePath] = Encoding.UTF8.GetString(attestation.AsSpan()),
        };
        if (spec.IncludeCasBlob)
        {
            var (casPath, casBytes) = DigestionTestSupport.CasFile(atom);
            files[casPath] = Encoding.UTF8.GetString(casBytes);
        }

        if (tailAuthPath is not null)
        {
            files[tailAuthPath] = Encoding.UTF8.GetString(tailAuthBytes.AsSpan());
        }

        // The baseline is always sibling-free: cross-atom binding (gate ⑤) is a
        // candidate-only conflict, so the sibling entry must not appear at base
        // (otherwise gate ②(b) would fire first).
        var baselineCoverage = spec.BaselineCoverageGid is not null
            ? ImmutableArray.Create(spec.BaselineCoverageGid)
            : spec.InitialCoverage;
        var baseline = new Dictionary<string, string>(files, StringComparer.Ordinal)
        {
            [BackfillInventoryLoader.RelativePath] =
                BuildLedger(spec, atom, baselineCoverage, includeOtherAtom: false, null, null),
        };

        // File-level declaration newness (gate ②c): by default the covered Lean
        // file is new relative to the baseline (absent). BaselineTargetIdentical
        // keeps it byte-identical at base so the declaration reads as not-new.
        if (!spec.BaselineTargetIdentical)
        {
            baseline.Remove(targetPath);
        }

        var declarations = spec.ReportDeclarations
            .Select(name => new LeanDeclaration(name, "theorem", "True", spec.TargetAxioms))
            .ToImmutableArray();
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [targetPath] = new LeanFileReport(ImmutableArray<string>.Empty, declarations),
        });

        var verified = spec.VerifyScribe
            ? VerifiedScribeEmissions.Create(
                [record],
                spec.Declaration is null ? [] : [spec.Gid])
            : VerifiedScribeEmissions.Empty;

        return new CoverInputs(files, baseline, report, verified, spec.Gid, ledger);
    }

    private static string BuildLedger(
        CoverSpec spec,
        DigestionAtom atom,
        ImmutableArray<string> coverage,
        bool includeOtherAtom,
        string? tailAuthPath,
        string? tailAuthSha)
    {
        var builder = new StringBuilder();
        builder.Append("schema_version: 3\n");
        builder.Append("ledger: theory-digestion-v1\n");
        builder.Append("sources:\n");
        builder.Append("  - source_id: fixture-source\n");
        builder.Append($"    path: {GoldenCorpus.FixtureDigestionSourcePath}\n");
        builder.Append($"    atomizer: {AtomizerRegistry.RegisteredIds[0]}\n");
        builder.Append("    acknowledged_stale: []\n");
        builder.Append("    entries:\n");
        AppendEntry(
            builder,
            spec.AtomId,
            atom.AstPath,
            atom.Fingerprints,
            coverage,
            spec.Migration,
            spec.Truth,
            tailAuthPath,
            tailAuthSha);
        if (includeOtherAtom && spec.OtherAtomBinding is { } other)
        {
            AppendEntry(
                builder,
                other.AtomId,
                "theorem/sibling",
                atom.Fingerprints,
                ImmutableArray.Create(other.Gid),
                "partial",
                "closed",
                null,
                null);
        }

        builder.Append("ticket_index: []\n");
        return builder.ToString();
    }

    private static void AppendEntry(
        StringBuilder builder,
        string atomId,
        string astPath,
        DigestionFingerprints fingerprints,
        ImmutableArray<string> coverage,
        string migration,
        string truth,
        string? tailAuthPath,
        string? tailAuthSha)
    {
        builder.Append($"      - atom_id: {atomId}\n");
        builder.Append($"        ast_path: {astPath}\n");
        builder.Append("        fingerprints:\n");
        builder.Append($"          raw_sha256: {fingerprints.RawSha256}\n");
        builder.Append($"          normalized_sha256: {fingerprints.NormalizedSha256}\n");
        builder.Append($"        cas_ref: {fingerprints.RawSha256}\n");
        if (coverage.Length == 0)
        {
            builder.Append("        coverage_gids: []\n");
        }
        else
        {
            builder.Append("        coverage_gids:\n");
            foreach (var gid in coverage)
            {
                builder.Append($"          - {gid}\n");
            }
        }

        builder.Append("        receipts:\n");
        builder.Append("          coverage: []\n");
        builder.Append("          scribe: []\n");
        builder.Append("          unresolved_subitems: []\n");
        builder.Append("          chain_atoms: []\n");
        if (tailAuthPath is not null && tailAuthSha is not null)
        {
            builder.Append("          tail_authorization:\n");
            builder.Append($"            path: {tailAuthPath}\n");
            builder.Append($"            sha256: {tailAuthSha}\n");
        }
        else
        {
            builder.Append("          tail_authorization: null\n");
        }

        builder.Append("        status:\n");
        builder.Append($"          migration: {migration}\n");
        builder.Append($"          truth: {truth}\n");
    }
}
