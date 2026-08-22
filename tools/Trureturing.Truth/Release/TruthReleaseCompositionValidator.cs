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
    }
}
