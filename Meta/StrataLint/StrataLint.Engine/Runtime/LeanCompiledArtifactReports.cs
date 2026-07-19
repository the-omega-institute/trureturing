namespace StrataLint.Engine;

public static class LeanCompiledArtifactReports
{
    public static LeanAxiomReport InspectRepository(string repositoryRoot) =>
        ReadRepository(repositoryRoot, ResolveReportPath(repositoryRoot));

    internal static string ResolveReportPath(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var configured = Environment.GetEnvironmentVariable("STRATALINT_LEAN_REPORT");
        return string.IsNullOrWhiteSpace(configured)
            ? RawLeanReportArtifact.DefaultPath(root)
            : Path.GetFullPath(configured, root);
    }

    public static LeanAxiomReport ReadRepository(string repositoryRoot, string? reportPath)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var artifactPath = reportPath is null
            ? RawLeanReportArtifact.DefaultPath(root)
            : Path.GetFullPath(reportPath, root);
        if (!File.Exists(artifactPath))
        {
            throw new InvalidOperationException(
                $"Precomputed raw Lean report is unavailable at {artifactPath}; "
                + "run `Meta/StrataLint/lean-inspector/inspect.sh --repository . "
                + "--output .lake/build/stratalint/raw-lean-report.json` first.");
        }

        var decoded = SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(root));
        if (decoded is SnapshotDecodeOutcome.InfrastructureFailure failure)
        {
            throw new InvalidOperationException(
                $"Repository snapshot for Lean inspection is unavailable: {failure.Message}");
        }

        return RawLeanReportArtifact.ReadFile(
            artifactPath,
            ((SnapshotDecodeOutcome.Decoded)decoded).Snapshot);
    }
}
