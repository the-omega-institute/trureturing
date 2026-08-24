using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class CanonicalScribeProducerSurface
{
    private static readonly TimeSpan ResolutionTimeout = TimeSpan.FromMinutes(2);
    private readonly Dictionary<RepositorySnapshot, ImmutableHashSet<string>> pathsBySnapshot =
        new(ReferenceEqualityComparer.Instance);

    internal bool HasIdenticalBytes(
        RepositorySnapshot baseline,
        RepositorySnapshot candidate)
    {
        var paths = Paths(baseline).Union(Paths(candidate), StringComparer.Ordinal);
        return paths.All(path => FileBytesIdentical(baseline, candidate, path));
    }

    private ImmutableHashSet<string> Paths(RepositorySnapshot snapshot)
    {
        if (pathsBySnapshot.TryGetValue(snapshot, out var paths))
        {
            return paths;
        }

        paths = ReadPaths(snapshot);
        pathsBySnapshot.Add(snapshot, paths);
        return paths;
    }

    private static ImmutableHashSet<string> ReadPaths(RepositorySnapshot snapshot)
    {
        using var materialized = MaterializedRepositorySnapshot.Create(snapshot);
        var script = Path.Combine(
            materialized.Root,
            "tools",
            "scripts",
            "report",
            "lean-report-input.sh");
        if (!File.Exists(script))
        {
            throw new InvalidOperationException(
                "canonical Scribe producer closure script is unavailable");
        }

        var result = BoundedProcessRunner.Run(
            "bash",
            [script, "scribe-producer-paths", "--repository", materialized.Root],
            materialized.Root,
            ResolutionTimeout,
            16 * 1024 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                "canonical Scribe producer closure is unavailable: "
                + Encoding.UTF8.GetString(result.StandardError).Trim());
        }

        var paths = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        foreach (var raw in Encoding.UTF8.GetString(result.StandardOutput)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
        {
            if (!RepoPath.TryCreate(raw, out var path)
                || !snapshot.TryGetFile(path.Value, out _)
                || !paths.Add(path.Value))
            {
                throw new InvalidOperationException(
                    "canonical Scribe producer closure emitted an invalid, absent, or duplicate path");
            }
        }

        return paths.Count > 0
            ? paths.ToImmutable()
            : throw new InvalidOperationException(
                "canonical Scribe producer closure is empty");
    }

    private static bool FileBytesIdentical(
        RepositorySnapshot baseline,
        RepositorySnapshot candidate,
        string path) =>
        baseline.TryGetFile(path, out var baselineFile)
        && candidate.TryGetFile(path, out var candidateFile)
        && baselineFile.RawBytes.AsSpan().SequenceEqual(candidateFile.RawBytes.AsSpan());
}
