using StrataLint.Engine;

namespace StrataLint.Scribe;

/// Projects the repository truth DAG to Generated/DAG.md.
///
/// The DAG is supplied by the caller rather than built here: constructing it needs a
/// RepositorySnapshot, which only the git gateway in StrataLint.Cli can produce. Enumerating the
/// working tree from this assembly instead would be a second, disagreeing source of truth about
/// what the repository contains.
public static class DagEmitter
{
    public const string RelativePath = "Generated/DAG.md";
    public const string TruthGraphRelativePath = "Generated/truth-graph.v1.json";

    public static int Emit(
        string repositoryRoot,
        AcyclicTruthDag dag,
        TruthGraphProvenance provenance,
        bool check,
        TextWriter output,
        TextWriter error,
        DocumentGraphExportProjection? documentProjection = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(dag);
        ArgumentNullException.ThrowIfNull(provenance);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);

        try
        {
            var model = TruthGraphExportModel.Create(dag, provenance, documentProjection);
            var markdown = CanonicalDagWriter.Write(dag);
            var markdownAgain = CanonicalDagWriter.Write(dag);
            var json = TruthGraphJsonWriter.Write(model);
            var jsonAgain = TruthGraphJsonWriter.Write(model);
            if (!markdown.AsSpan().SequenceEqual(markdownAgain.AsSpan())
                || !json.AsSpan().SequenceEqual(jsonAgain.AsSpan()))
            {
                throw new InvalidOperationException("DAG projection writer is not byte deterministic.");
            }

            var projections = new[]
            {
                (Path: RelativePath, Bytes: markdown),
                (Path: TruthGraphRelativePath, Bytes: json),
            };
            var stale = projections.Where(projection =>
            {
                if (check && projection.Path == RelativePath)
                {
                    return false;
                }
                var path = Path.Combine(repositoryRoot, projection.Path);
                var current = File.Exists(path) ? File.ReadAllBytes(path) : [];
                return !current.AsSpan().SequenceEqual(projection.Bytes.AsSpan());
            }).ToArray();

            if (check && stale.Length > 0)
            {
                foreach (var projection in stale)
                {
                    error.WriteLine("out of date: " + projection.Path);
                }

                return 1;
            }


            if (check)
            {
                output.WriteLine("rebuilt twice: " + RelativePath);
            }

            foreach (var projection in stale)
            {
                var path = Path.Combine(repositoryRoot, projection.Path);
                var parent = Path.GetDirectoryName(path)
                    ?? throw new InvalidOperationException("DAG projection path has no parent directory.");
                Directory.CreateDirectory(parent);
                File.WriteAllBytes(path, projection.Bytes.AsSpan());
                output.WriteLine("wrote: " + projection.Path);
            }

            foreach (var projection in projections.Except(stale))
            {
                output.WriteLine("checked: " + projection.Path);
            }

            return 0;
        }
        catch (Exception exception) when (
            exception is InvalidOperationException
                or IOException
                or UnauthorizedAccessException
                or ArgumentException
                or FormatException)
        {
            error.WriteLine("dag emit failed: " + exception.Message);
            return 2;
        }
    }
}
