using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static partial class CoverWorld
{
    private static List<ScribeEmissionRecord> MaterializeScribeRecords(
        CoverSpec spec,
        ScribeEmissionRecord primary)
    {
        var records = new List<ScribeEmissionRecord> { primary };
        if (spec.SecondaryTarget is { } secondary)
        {
            var definition = System.Text.Encoding.UTF8.GetBytes("secondary scribe definition\n");
            var emission = System.Text.Encoding.UTF8.GetBytes("# secondary emitted narrative\n");
            records.Add(new ScribeEmissionRecord(
                secondary.ModuleGid,
                ScribeEmissionAttestation.DefinitionPath(secondary.ModuleGid),
                DigestionFingerprint.Compute(definition).RawSha256,
                ScribeEmissionAttestation.EmissionPath(secondary.ModuleGid),
                DigestionFingerprint.Compute(emission).RawSha256));
        }

        return records;
    }

    private static void MaterializeSecondaryFiles(CoverSpec spec, IDictionary<string, string> files)
    {
        if (spec.SecondaryTarget is not { } secondary)
        {
            return;
        }

        files[secondary.ModuleGid + ".lean"] = DigestionTestSupport.Lean(secondary.ModuleGid);
        files[ScribeEmissionAttestation.DefinitionPath(secondary.ModuleGid)] =
            "secondary scribe definition\n";
        files[ScribeEmissionAttestation.EmissionPath(secondary.ModuleGid)] =
            "# secondary emitted narrative\n";
    }

    private static LeanAxiomReport MaterializeReport(
        CoverSpec spec,
        string targetPath,
        ImmutableArray<LeanDeclaration> primaryDeclarations)
    {
        var reportFiles = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [targetPath] = new LeanFileReport(ImmutableArray<string>.Empty, primaryDeclarations),
        };
        if (spec.SecondaryTarget is { } secondary)
        {
            reportFiles[secondary.ModuleGid + ".lean"] = new LeanFileReport(
                ImmutableArray<string>.Empty,
                [new LeanDeclaration(
                    secondary.Declaration,
                    "theorem",
                    "True",
                    ImmutableArray<string>.Empty)]);
        }

        return LeanAxiomReport.Create(reportFiles);
    }

    private static IEnumerable<string> MaterializeVerifiedGids(CoverSpec spec) =>
        (spec.Declaration is null ? [] : new[] { spec.Gid })
            .Concat(spec.SecondaryTarget is { } secondary
                ? [secondary.ModuleGid + "." + secondary.Declaration]
                : []);

    private static BackfillInventoryDocument BuildLedger(
        CoverSpec spec,
        DigestionAtom atom,
        ImmutableArray<string> coverage,
        bool includeOtherAtom,
        string? tailAuthPath,
        string? tailAuthSha,
        Func<string, string>? coverageStatementId = null,
        DigestionAtom? otherAtom = null,
        string? otherSourcePath = null,
        DigestionAtom? unrelatedAtom = null,
        string? unrelatedSourcePath = null,
        bool useUnrelatedBaselineCoverage = false)
    {
        var sources = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        var entries = ImmutableArray.CreateBuilder<DigestionLedgerEntry>();
        entries.Add(Entry(
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            spec.AtomId,
            atom.Fingerprints,
            coverage,
            spec.Migration,
            spec.Truth,
            tailAuthPath,
            tailAuthSha,
            coverage.Length == 1 ? coverageStatementId?.Invoke(coverage[0]) : null,
            spec.InitialDefinitionSha256,
            spec.InitialEmissionSha256,
            spec.InitialUnresolvedSubitems));
        sources.Add(new DigestionLedgerSource(
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            SyntheticNumberedAtomizer.Id,
            [],
            GenreRegistryProjection.Available(GenreRegistryCheck.Collected([])),
            entries.ToImmutable()));

        if (includeOtherAtom
            && spec.OtherAtomGid is { } otherGid
            && otherAtom is not null
            && otherSourcePath is not null)
        {
            sources.Add(new DigestionLedgerSource(
                "fixture-sibling-source",
                otherSourcePath,
                SyntheticNumberedAtomizer.Id,
                [],
                GenreRegistryProjection.Available(GenreRegistryCheck.Collected([])),
                [
                    Entry(
                        "fixture-sibling-source",
                        otherSourcePath,
                        CoverWorld.OtherAtomId,
                        otherAtom.Fingerprints,
                        [otherGid],
                        spec.OtherMigration,
                        spec.OtherTruth,
                        null,
                        null,
                        coverageStatementId?.Invoke(otherGid),
                        spec.InitialDefinitionSha256,
                        spec.InitialEmissionSha256,
                        []),
                ]));
        }

        if (spec.UnrelatedSibling is { } sibling
            && unrelatedAtom is not null
            && unrelatedSourcePath is not null)
        {
            var siblingCoverage = useUnrelatedBaselineCoverage
                ? sibling.BaselineCoverage
                : sibling.CurrentCoverage;
            sources.Add(new DigestionLedgerSource(
                "fixture-unrelated-source",
                unrelatedSourcePath,
                SyntheticNumberedAtomizer.Id,
                [],
                GenreRegistryProjection.Available(GenreRegistryCheck.Collected([])),
                [
                    Entry(
                        "fixture-unrelated-source",
                        unrelatedSourcePath,
                        CoverWorld.UnrelatedAtomId,
                        unrelatedAtom.Fingerprints,
                        siblingCoverage,
                        "partial",
                        "closed",
                        null,
                        null,
                        null,
                        null,
                        null,
                        sibling.UnresolvedSubitems),
                ]));
        }

        return BackfillInventoryDocument.Create(sources.ToImmutable(), []);
    }

    private static DigestionLedgerEntry Entry(
        string sourceId,
        string sourcePath,
        string atomId,
        DigestionFingerprints fingerprints,
        ImmutableArray<string> coverage,
        string migration,
        string truth,
        string? tailAuthPath,
        string? tailAuthSha,
        string? targetStatementId,
        string? definitionSha256,
        string? emissionSha256,
        ImmutableArray<string> unresolvedSubitems)
    {
        var coverageEdges = coverage
            .Select(gid => new DigestionCoverageEdge(gid, targetStatementId))
            .ToImmutableArray();
        var scribeReceipts = coverage.Length == 1
            && definitionSha256 is not null
            && emissionSha256 is not null
                ? ImmutableArray.Create(new DigestionScribeReceipt(
                    coverage[0],
                    definitionSha256,
                    emissionSha256))
                : [];
        var tailAuthorization = tailAuthPath is not null && tailAuthSha is not null
            ? new DigestionExternalReceipt(tailAuthPath, tailAuthSha)
            : null;
        return new DigestionLedgerEntry(
            sourceId,
            sourcePath,
            SyntheticNumberedAtomizer.Id,
            atomId,
            fingerprints,
            coverageEdges,
            new DigestionReceipts(
                scribeReceipts,
                unresolvedSubitems,
                [],
                tailAuthorization),
            new DigestionStatus(Migration(migration), Truth(truth)),
            fingerprints.RawSha256);
    }

    private static string FrozenStatementIdFor(CoverSpec spec, string gid)
    {
        if (Gid.TryParse(gid, out var parsed)
            && parsed.ToTarget() is Target.Formal { Declaration: null })
        {
            return FrozenStatementReceiptTestData.Id('b');
        }

        return string.Equals(gid, spec.Gid, StringComparison.Ordinal)
            ? spec.TargetStatementId
            : FrozenStatementReceiptTestData.Id('c');
    }

    private static void MaterializeFrozenLedger(
        CoverSpec spec,
        LeanAxiomReport report,
        string targetPath,
        IDictionary<string, string> files,
        IDictionary<string, string> baseline)
    {
        var frozenModules = report.Files
            .Where(file => spec.FreezeTargetModule
                || !string.Equals(file.Key.Value, targetPath, StringComparison.Ordinal))
            .Select(file =>
            {
                var declarations = file.Value.Declarations.Select(declaration =>
                    new FrozenStatementReceiptTestData.Declaration(
                        declaration.Name[(declaration.Name.LastIndexOf('.') + 1)..],
                        string.Equals(file.Key.Value, targetPath, StringComparison.Ordinal)
                            && string.Equals(
                                declaration.Name[(declaration.Name.LastIndexOf('.') + 1)..],
                                spec.Declaration,
                                StringComparison.Ordinal)
                                ? spec.TargetStatementId
                                : FrozenStatementReceiptTestData.Id('c')))
                    .ToList();
                if (string.Equals(file.Key.Value, targetPath, StringComparison.Ordinal)
                    && spec.Declaration is not null
                    && declarations.All(item => !string.Equals(
                        item.Selector,
                        spec.Declaration,
                        StringComparison.Ordinal)))
                {
                    declarations.Add(new FrozenStatementReceiptTestData.Declaration(
                        spec.Declaration,
                        spec.TargetStatementId));
                }

                return new FrozenStatementReceiptTestData.Module(
                    file.Key.Value,
                    FrozenStatementReceiptTestData.Id('b'),
                    declarations.ToImmutableArray());
            })
            .ToArray();
        FrozenStatementReceiptTestData.AddLedger(files, frozenModules);
        var baselineModules = spec.FrozenTargetInBaseline
            ? frozenModules
            : frozenModules.Where(module => !string.Equals(
                module.Path,
                targetPath,
                StringComparison.Ordinal)).ToArray();
        if (baselineModules.Length > 0)
        {
            FrozenStatementReceiptTestData.AddLedger(baseline, baselineModules);
        }
    }

    private static DigestionMigrationState Migration(string value) => value switch
    {
        "residual" => DigestionMigrationState.Residual,
        "partial" => DigestionMigrationState.Partial,
        "absorbed" => DigestionMigrationState.Absorbed,
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };

    private static DigestionTruthState Truth(string value) => value switch
    {
        "closed" => DigestionTruthState.Closed,
        "tail" => DigestionTruthState.Tail,
        "open" => DigestionTruthState.Open,
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };
}
