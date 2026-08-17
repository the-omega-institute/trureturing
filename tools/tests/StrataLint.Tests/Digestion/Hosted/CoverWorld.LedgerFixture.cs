using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static partial class CoverWorld
{
    private static BackfillInventoryDocument BuildLedger(
        CoverSpec spec,
        DigestionAtom atom,
        ImmutableArray<string> coverage,
        bool includeOtherAtom,
        string? tailAuthPath,
        string? tailAuthSha,
        string? targetSha256 = null,
        DigestionAtom? hostedAtom = null,
        string? hostedSourcePath = null,
        bool useHostedBaselineCoverage = false)
    {
        var sources = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        var entries = ImmutableArray.CreateBuilder<DigestionLedgerEntry>();
        entries.Add(Entry(
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            spec.AtomId,
            atom.AstPath,
            atom.Fingerprints,
            coverage,
            spec.Migration,
            spec.Truth,
            tailAuthPath,
            tailAuthSha,
            targetSha256,
            spec.InitialDefinitionSha256,
            spec.InitialEmissionSha256,
            spec.InitialUnresolvedSubitems));
        if (includeOtherAtom && spec.OtherAtomBinding is { } other)
        {
            entries.Add(Entry(
                "fixture-source",
                RuleFixture.FixtureDigestionSourcePath,
                other.AtomId,
                "theorem/sibling",
                atom.Fingerprints,
                [other.Gid],
                "partial",
                "closed",
                null,
                null,
                null,
                null,
                null,
                []));
        }

        sources.Add(new DigestionLedgerSource(
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            SyntheticNumberedAtomizer.Id,
            [],
            GenreRegistryProjection.Available(GenreRegistryCheck.Collected([])),
            entries.ToImmutable()));

        if (spec.HostedSibling is { } hostedSibling
            && hostedAtom is not null
            && hostedSourcePath is not null)
        {
            var hostedCoverage = useHostedBaselineCoverage
                ? hostedSibling.BaselineCoverage
                : hostedSibling.CurrentCoverage;
            sources.Add(new DigestionLedgerSource(
                "fixture-hosted-source",
                hostedSourcePath,
                SyntheticNumberedAtomizer.Id,
                [],
                GenreRegistryProjection.Available(GenreRegistryCheck.Collected([])),
                [
                    Entry(
                        "fixture-hosted-source",
                        hostedSourcePath,
                        hostedSibling.AtomId,
                        hostedAtom.AstPath,
                        hostedAtom.Fingerprints,
                        hostedCoverage,
                        "partial",
                        "closed",
                        null,
                        null,
                        null,
                        null,
                        null,
                        hostedSibling.UnresolvedSubitems),
                ]));
        }

        return BackfillInventoryDocument.Create(sources.ToImmutable(), []);
    }

    private static DigestionLedgerEntry Entry(
        string sourceId,
        string sourcePath,
        string atomId,
        string astPath,
        DigestionFingerprints fingerprints,
        ImmutableArray<string> coverage,
        string migration,
        string truth,
        string? tailAuthPath,
        string? tailAuthSha,
        string? targetSha256,
        string? definitionSha256,
        string? emissionSha256,
        ImmutableArray<string> unresolvedSubitems)
    {
        var coverageReceipts = coverage.Length == 1 && targetSha256 is not null
            ? ImmutableArray.Create(new DigestionCoverageReceipt(
                coverage[0],
                fingerprints.RawSha256,
                targetSha256))
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
            astPath,
            null,
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
