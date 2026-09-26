using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class ValuesEmitter
{
    public static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);

        try
        {
            var first = CanonicalValuesWriter.Write(repositoryRoot);
            var second = CanonicalValuesWriter.Write(repositoryRoot);
            if (first.Length != second.Length || first.Zip(second).Any(pair =>
                pair.First.Id != pair.Second.Id || pair.First.RelativePath != pair.Second.RelativePath
                || !pair.First.Bytes.AsSpan().SequenceEqual(pair.Second.Bytes.AsSpan())))
            {
                throw new InvalidOperationException("Values writer is not byte deterministic.");
            }

            if (check)
            {
                output.WriteLine("verified: values producer is byte deterministic");
                return 0;
            }

            foreach (var projection in first)
            {
                var path = Path.Combine(repositoryRoot, projection.RelativePath);
                var current = File.Exists(path) ? File.ReadAllBytes(path) : [];
                if (current.AsSpan().SequenceEqual(projection.Bytes.AsSpan()))
                {
                    output.WriteLine("checked: " + projection.RelativePath);
                    continue;
                }
                Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                File.WriteAllBytes(path, projection.Bytes.ToArray());
                output.WriteLine("wrote: " + projection.RelativePath);
            }

            // Removing a key removes its producer-owned shard. Inventory still derives keys
            // from the catalog; it does not admit arbitrary files already in this directory.
            var directory = Path.Combine(repositoryRoot, ValuesProjectionAddress.DirectoryPath);
            var expected = first.Select(static row => row.RelativePath).ToHashSet(StringComparer.Ordinal);
            if (Directory.Exists(directory))
            {
                foreach (var path in Directory.EnumerateFiles(directory).Order(StringComparer.Ordinal))
                {
                    var relative = Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/');
                    if (ValuesProjectionAddress.TryIdFromPath(relative, out _) && !expected.Contains(relative))
                    {
                        File.Delete(path);
                        output.WriteLine("removed: " + relative);
                    }
                }
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
            error.WriteLine("values emit failed: " + exception.Message);
            return 1;
        }
    }
}
