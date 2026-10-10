namespace StrataLint.Engine;

public static class LeanCompiledArtifactReports
{
    public static LeanAxiomReport ReadRepositoryFiles(string repositoryRoot, string? reportPath = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var artifactPath = reportPath is null
            ? ResolveReportPath(root)
            : Path.GetFullPath(reportPath, root);
        if (!File.Exists(artifactPath))
        {
            throw new InvalidOperationException(
                $"Precomputed raw Lean report is unavailable at {artifactPath}; "
                + "run `tools/lean-inspector/inspect.sh --repository . "
                + "--output .lake/build/stratalint/raw-lean-report.json` first.");
        }

        return RawLeanReportArtifact.ReadFile(artifactPath, ReadSources(root));
    }

    public static LeanAxiomReport ReadScopedRepositoryFiles(
        string repositoryRoot, IEnumerable<string> targetPaths, string? reportPath = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(targetPaths);
        var root = Path.GetFullPath(repositoryRoot);
        var artifactPath = reportPath is null ? ResolveReportPath(root) : Path.GetFullPath(reportPath, root);
        var scope = LeanReportScope.Create(ReadSources(root), targetPaths.Select(RepoPath.CreateKnown));
        var report = RawLeanReportArtifact.ReadFileForScope(artifactPath, scope, validateMaterials: true);
        return LeanClosureValidator.Validate(scope.SourceSnapshot, report) switch
        {
            LeanValidationOutcome.Accepted => report,
            LeanValidationOutcome.InfrastructureFailure failure => throw new InvalidOperationException(failure.Message),
            _ => throw new InvalidOperationException("Unknown scoped Lean validation outcome."),
        };
    }

    // Source indexing does not compile or extract unselected modules.
    private static RepositorySnapshot ReadSources(string root)
    {
        var paths = new[] { "D5", "Reg" }
            .Select(directory => Path.Combine(root, directory))
            .Where(Directory.Exists)
            .SelectMany(directory => Directory.EnumerateFiles(directory, "*.lean", SearchOption.AllDirectories));
        var rootModule = Path.Combine(root, "Trureturing.lean");
        if (File.Exists(rootModule)) paths = paths.Append(rootModule);
        var raw = RawRepositorySnapshot.Create(paths.Select(path => new RawRepositoryEntry(
            Path.GetRelativePath(root, path).Replace('\\', '/'),
            System.Collections.Immutable.ImmutableArray.CreateRange(File.ReadAllBytes(path)))));
        var decoded = SnapshotDecoder.Decode(raw);
        if (decoded is SnapshotDecodeOutcome.InfrastructureFailure failure)
        {
            throw new InvalidOperationException(
                $"Repository snapshot for Lean inspection is unavailable: {failure.Message}");
        }

        return ((SnapshotDecodeOutcome.Decoded)decoded).Snapshot;
    }

    internal static string ResolveReportPath(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var configured = Environment.GetEnvironmentVariable("STRATALINT_LEAN_REPORT");
        return string.IsNullOrWhiteSpace(configured)
            ? RawLeanReportArtifact.DefaultPath(root)
            : Path.GetFullPath(configured, root);
    }

}
