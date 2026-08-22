namespace Trureturing.Truth;

internal static class TruthReleaseCompositionValidator
{
    internal static void Validate(
        SourceSnapshotModel sourceSnapshot,
        TruthExportModel truthExport,
        TruthReleaseManifest manifest,
        string computedTruthGraphDigest)
    {
        ArgumentNullException.ThrowIfNull(sourceSnapshot);
        ArgumentNullException.ThrowIfNull(truthExport);
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(computedTruthGraphDigest);

        if (!string.Equals(sourceSnapshot.SourceCommit, truthExport.SourceCommit, StringComparison.Ordinal)
            || !string.Equals(sourceSnapshot.SourceCommit, manifest.Source.SourceCommit, StringComparison.Ordinal))
        {
            throw new FormatException(
                "Truth release source_commit disagrees across source_snapshot, truth_export, and manifest.");
        }

        if (!string.Equals(sourceSnapshot.SourceTree, truthExport.SourceTree, StringComparison.Ordinal)
            || !string.Equals(sourceSnapshot.SourceTree, manifest.Source.SourceTree, StringComparison.Ordinal))
        {
            throw new FormatException(
                "Truth release source_tree disagrees across source_snapshot, truth_export, and manifest.");
        }

        if (!string.Equals(sourceSnapshot.TruthGraphSha256, computedTruthGraphDigest, StringComparison.Ordinal)
            || !string.Equals(computedTruthGraphDigest, manifest.Artifacts.TruthGraph.Sha256, StringComparison.Ordinal))
        {
            throw new FormatException(
                "Truth release truth_graph digest disagrees across source_snapshot, verified bytes, and manifest.");
        }

        // Artifact verification already proved that each manifest digest names the verified file bytes,
        // so these comparisons bind the snapshot's self-asserted digests to the actual bundle artifacts.
        if (!string.Equals(
                sourceSnapshot.RawLeanReportSha256,
                manifest.Artifacts.RawLeanReport.Sha256,
                StringComparison.Ordinal))
        {
            throw new FormatException(
                "Truth release raw_lean_report digest disagrees between source_snapshot and verified artifact bytes.");
        }

        if (!string.Equals(
                sourceSnapshot.ResidualFrontierSha256,
                manifest.Artifacts.ResidualFrontier.Sha256,
                StringComparison.Ordinal))
        {
            throw new FormatException(
                "Truth release residual_frontier digest disagrees between source_snapshot and verified artifact bytes.");
        }

        // Phase 2 deliberately leaves three fields unbound: FrozenLedgerHeadHash may be a content hash,
        // not the frozen-ledger-head.json file digest; DagMdSha256 has no bundle artifact because DAG.md
        // is an external derived document; and DeclarationsSha256 has no declarations artifact, so its
        // relationship to truth_export must first be pinned by the Phase 2 producer.
    }
}
