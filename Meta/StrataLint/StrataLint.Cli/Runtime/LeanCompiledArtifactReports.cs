using StrataLint.Engine;

namespace StrataLint.Cli;

public static class LeanCompiledArtifactReports
{
    public static LeanAxiomReport InspectRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var rootOlean = Path.Combine(
            root,
            ".lake",
            "build",
            "lib",
            "lean",
            "Trureturing.olean");
        if (!File.Exists(rootOlean))
        {
            throw new InvalidOperationException(
                "Lean compiled artifacts are unavailable under .lake/build/lib/lean; "
                + "run `lake build` before Scribe emit.");
        }

        var decoded = SnapshotDecoder.Decode(new GitRepositoryGateway(root).ReadCurrent());
        if (decoded is SnapshotDecodeOutcome.InfrastructureFailure failure)
        {
            throw new InvalidOperationException(
                $"Repository snapshot for Lean inspection is unavailable: {failure.Message}");
        }

        return new LeanProcessInspector(root).Inspect(
            ((SnapshotDecodeOutcome.Decoded)decoded).Snapshot);
    }
}
