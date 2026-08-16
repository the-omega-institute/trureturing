using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static partial class CoverWorld
{
    private static string BuildLedger(
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
        var builder = new StringBuilder();
        builder.Append("schema_version: 3\n");
        builder.Append("ledger: theory-digestion-v1\n");
        builder.Append("sources:\n");
        builder.Append("  - source_id: fixture-source\n");
        builder.Append($"    path: {RuleFixture.FixtureDigestionSourcePath}\n");
        builder.Append($"    atomizer: {SyntheticNumberedAtomizer.Id}\n");
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
            tailAuthSha,
            targetSha256,
            spec.InitialDefinitionSha256,
            spec.InitialEmissionSha256,
            spec.InitialUnresolvedSubitems);
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
                null,
                null,
                null,
                null,
                []);
        }

        if (spec.HostedSibling is { } hostedSibling && hostedAtom is not null && hostedSourcePath is not null)
        {
            builder.Append("  - source_id: fixture-hosted-source\n");
            builder.Append($"    path: {hostedSourcePath}\n");
            builder.Append($"    atomizer: {SyntheticNumberedAtomizer.Id}\n");
            builder.Append("    acknowledged_stale: []\n");
            builder.Append("    entries:\n");
            AppendEntry(
                builder,
                hostedSibling.AtomId,
                hostedAtom.AstPath,
                hostedAtom.Fingerprints,
                useHostedBaselineCoverage
                    ? hostedSibling.BaselineCoverage
                    : hostedSibling.CurrentCoverage,
                "partial",
                "closed",
                null,
                null,
                null,
                null,
                null,
                hostedSibling.UnresolvedSubitems);
        }

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
        string? tailAuthSha,
        string? targetSha256,
        string? definitionSha256,
        string? emissionSha256,
        ImmutableArray<string> unresolvedSubitems)
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
        if (coverage.Length == 1 && targetSha256 is not null)
        {
            builder.Append("          coverage:\n");
            builder.Append($"            - gid: {coverage[0]}\n");
            builder.Append($"              source_sha256: {fingerprints.RawSha256}\n");
            builder.Append($"              target_sha256: {targetSha256}\n");
        }
        else
        {
            builder.Append("          coverage: []\n");
        }

        if (coverage.Length == 1 && definitionSha256 is not null && emissionSha256 is not null)
        {
            builder.Append("          scribe:\n");
            builder.Append($"            - gid: {coverage[0]}\n");
            builder.Append($"              definition_sha256: {definitionSha256}\n");
            builder.Append($"              emission_sha256: {emissionSha256}\n");
        }
        else
        {
            builder.Append("          scribe: []\n");
        }
        if (unresolvedSubitems.Length == 0)
        {
            builder.Append("          unresolved_subitems: []\n");
        }
        else
        {
            builder.Append("          unresolved_subitems:\n");
            foreach (var subitem in unresolvedSubitems)
            {
                builder.Append($"            - {subitem}\n");
            }
        }
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
