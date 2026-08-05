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

    public static int Emit(
        string repositoryRoot,
        AcyclicTruthDag dag,
        bool check,
        TextWriter output,
        TextWriter error)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(dag);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);

        try
        {
            var first = CanonicalDagWriter.Write(dag);
            var second = CanonicalDagWriter.Write(dag);
            if (!first.AsSpan().SequenceEqual(second.AsSpan()))
            {
                throw new InvalidOperationException("DAG projection writer is not byte deterministic.");
            }

            var path = Path.Combine(repositoryRoot, RelativePath);
            var current = File.Exists(path) ? File.ReadAllBytes(path) : [];
            if (current.AsSpan().SequenceEqual(first.AsSpan()))
            {
                output.WriteLine("checked: " + RelativePath);
                return 0;
            }

            if (check)
            {
                error.WriteLine("out of date: " + RelativePath);
                return 1;
            }

            var parent = Path.GetDirectoryName(path)
                ?? throw new InvalidOperationException("DAG projection path has no parent directory.");
            Directory.CreateDirectory(parent);
            File.WriteAllBytes(path, first.AsSpan());
            output.WriteLine("wrote: " + RelativePath);
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
