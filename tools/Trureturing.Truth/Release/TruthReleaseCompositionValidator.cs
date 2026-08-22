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

        if (!string.Equals(
                sourceSnapshot.DeclarationsSha256,
                manifest.Artifacts.TruthExport.Sha256,
                StringComparison.Ordinal))
        {
            throw new FormatException(
                "Truth release declarations digest disagrees between source_snapshot and verified artifact bytes.");
        }

        if (!string.Equals(
                sourceSnapshot.FrozenLedgerHeadHash,
                manifest.Artifacts.FrozenLedgerHead.Sha256,
                StringComparison.Ordinal))
        {
            throw new FormatException(
                "Truth release frozen_ledger_head digest disagrees between source_snapshot and verified artifact bytes.");
        }

        // DagMdSha256 remains unbound because the bundle has no dag_md artifact. DAG.md is an external
        // derived document, so this field is self-asserted external provenance, not a bundle-coherence claim.
    }
}
