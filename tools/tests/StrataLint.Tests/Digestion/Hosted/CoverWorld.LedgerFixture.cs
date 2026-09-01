using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static partial class CoverWorld
{
    private static void MaterializeOtherAtomFormalizationReceipt(
        CoverSpec spec,
        DigestionAtom? atom,
        IDictionary<string, string> files)
    {
        if (spec.OtherAtomGid is not { } gid || atom is null)
        {
            return;
        }

        var separator = gid.LastIndexOf('.');
        var receipt = new DigestionFormalizationReceipt(
            CoverWorld.OtherAtomId,
            gid,
            new DigestionFormalizationSignature(
                gid[(separator + 1)..],
                spec.ReportKind,
                spec.ReportType),
            atom.Fingerprints.RawSha256,
            atom.Fingerprints.RawSha256);
        files[DigestionFormalizationReceipt.PathForAtom(CoverWorld.OtherAtomId)] =
            System.Text.Encoding.UTF8.GetString(
                DigestionFormalizationReceipt.Write(receipt).AsSpan());
    }

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
        var coverageReceipts = coverage.Length == 1 && targetStatementId is not null
            ? ImmutableArray.Create(new DigestionCoverageReceipt(
                coverage[0],
                fingerprints.RawSha256,
                targetStatementId))
            : [];
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
            coverage,
            new DigestionReceipts(
                coverageReceipts,
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
        FrozenStatementReceiptTestData.AddLedger(baseline, frozenModules);
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
