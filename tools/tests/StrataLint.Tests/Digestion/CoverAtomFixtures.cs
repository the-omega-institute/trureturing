using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// CoverAtomTests.cs 的共享夹具:CoverWorld(15 个测试文件消费)、CoverSpec(11)及其同族记录。
// 它们此前住在一个以某测试类命名的文件里,消费面却比那个测试类大 ——
// 按文件名找不到。纯搬迁:类型、可见性、成员逐字不变;本文件不含测试方法。

internal sealed record CoverInputs(
    Dictionary<string, string> Files,
    Dictionary<string, string> Baseline,
    LeanAxiomReport Report,
    VerifiedScribeEmissions? VerifiedEmissions,
    string Gid,
    string Ledger,
    BackfillInventoryDocument Document);

internal sealed record CoverUnrelatedSiblingSpec(
    ImmutableArray<string> CurrentCoverage,
    ImmutableArray<string> BaselineCoverage,
    ImmutableArray<string> UnresolvedSubitems);

// Declarative fixture for the cover gate matrix. Defaults produce a clean happy
// path (an open, CAS-backed residual atom whose target declaration is proven
// closed and Scribe-emitted); each gate test flips exactly one field.
internal sealed partial record CoverSpec
{
    internal string AtomId => CoverWorld.DefaultAtomId;

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

    internal string ReportKind { get; init; } = "theorem";

    internal string ReportType { get; init; } = "True";

    internal ImmutableArray<string> TargetAxioms { get; init; } = ImmutableArray<string>.Empty;
    internal bool VerifyScribe { get; init; } = true;
    internal string? BaselineCoverageGid { get; init; }

    internal string? OtherAtomGid { get; init; }

    internal string OtherMigration { get; init; } = "partial";

    internal string OtherTruth { get; init; } = "closed";

    // When true the residual entry carries a verified tail authorization, so a
    // target proven only with a non-standard axiom (Tail) derives an
    // absorbed-tail deletable state. Used to prove gate (6) rejects Tail.
    internal bool TailAuthorized { get; init; }

    // When true the baseline holds the covered declaration's Lean file with
    // identical bytes (the declaration is not new). Default: the file is new
    // relative to the baseline (absent), which is the ordinary cover case.
    internal bool BaselineTargetIdentical { get; init; }

    internal (string ModuleGid, string Declaration)? SecondaryTarget { get; init; }

    internal CoverUnrelatedSiblingSpec? UnrelatedSibling { get; init; }

    internal string Gid => Declaration is null ? ModuleGid : ModuleGid + "." + Declaration;

    internal CoverInputs Materialize() => CoverWorld.Materialize(this);
}

internal static partial class CoverWorld
{
    private const string DefaultSourceText =
        "# Synthetic\n\n**定理 1.1(A)**。cover fixture atom body。\n";
    private const string OtherSourceText =
        "# Synthetic\n\n**定理 1.1(A)**。cover sibling atom body。\n";
    private const string UnrelatedSourceText =
        "# Synthetic\n\n**定理 1.1(A)**。unrelated sibling atom body。\n";
    private const string OtherSourcePath = "docs/COVER_SIBLING.md";
    private const string UnrelatedSourcePath = "docs/CONTRIBUTING.md";
    private const string GovernanceDocumentAnchor = "  - \"docs/CONTRIBUTING.md\"\n";

    internal static readonly string DefaultAtomId = AtomIdFor(DefaultSourceText);
    internal static readonly string OtherAtomId = AtomIdFor(OtherSourceText);
    internal static readonly string UnrelatedAtomId = AtomIdFor(UnrelatedSourceText);
    internal static readonly DateTimeOffset FixtureUtc = new(2026, 8, 26, 4, 3, 2, TestBudgets.ZeroDuration);
    internal static TimeProvider TimeProvider { get; } = new FixedTimeProvider(FixtureUtc);

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
        var sourceBytes = Encoding.UTF8.GetBytes(DefaultSourceText);
        var atom = Assert.Single(
            AtomizerRegistry.Atomize(SyntheticNumberedAtomizer.Id, sourceBytes, DigestionTestSupport.Rules).Claims);
        var otherSourceBytes = Encoding.UTF8.GetBytes(OtherSourceText);
        var otherAtom = spec.OtherAtomGid is null
            ? null
            : Assert.Single(AtomizerRegistry.Atomize(
                SyntheticNumberedAtomizer.Id,
                otherSourceBytes,
                DigestionTestSupport.Rules).Claims);
        var unrelatedSourceBytes = Encoding.UTF8.GetBytes(UnrelatedSourceText);
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
            otherAtom,
            OtherSourcePath,
            unrelatedAtom,
            UnrelatedSourcePath,
            useUnrelatedBaselineCoverage: false);
        var ledger = DirectoryLedgerTestSupport.Image(document);
        var registry = spec.OtherAtomGid is null
            ? TestRegistry.Canonical
            : TestRegistry.Canonical.Replace(
                GovernanceDocumentAnchor,
                GovernanceDocumentAnchor + $"  - \"{OtherSourcePath}\"\n",
                StringComparison.Ordinal);
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Meta/registry.yaml"] = registry,
            ["Meta/domains.yaml"] = TestRegistry.Domains,
            [RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes),
            [targetPath] = Encoding.UTF8.GetString(targetBytes),
            [ScribeEmissionAttestation.DefinitionPath(spec.ModuleGid)] = Encoding.UTF8.GetString(definition),
            [ScribeEmissionAttestation.EmissionPath(spec.ModuleGid)] = Encoding.UTF8.GetString(emission),
            [ScribeEmissionAttestation.RelativePath] = Encoding.UTF8.GetString(attestation.AsSpan()),
        };
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        if (otherAtom is not null)
        {
            files[OtherSourcePath] = Encoding.UTF8.GetString(otherSourceBytes);
            var (otherCasPath, otherCasBytes) = DigestionTestSupport.CasFile(otherAtom);
            files[otherCasPath] = Encoding.UTF8.GetString(otherCasBytes);
        }
        if (unrelatedAtom is not null)
        {
            files[UnrelatedSourcePath] = Encoding.UTF8.GetString(unrelatedSourceBytes);
            var (unrelatedCasPath, unrelatedCasBytes) = DigestionTestSupport.CasFile(unrelatedAtom);
            files[unrelatedCasPath] = Encoding.UTF8.GetString(unrelatedCasBytes);
        }
        MaterializeSecondaryFiles(spec, files);
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
            otherAtom: null,
            otherSourcePath: OtherSourcePath,
            unrelatedAtom: unrelatedAtom,
            unrelatedSourcePath: UnrelatedSourcePath,
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
            ledger,
            document);
    }

    private static string AtomIdFor(string sourceText)
    {
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            SyntheticNumberedAtomizer.Id,
            Encoding.UTF8.GetBytes(sourceText),
            DigestionTestSupport.Rules).Claims);
        return atom.Fingerprints.RawSha256["sha256:".Length..];
    }

}

internal sealed class FixedTimeProvider(DateTimeOffset utcNow) : TimeProvider { public override DateTimeOffset GetUtcNow() => utcNow; }
