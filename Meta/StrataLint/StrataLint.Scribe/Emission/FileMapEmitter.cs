namespace StrataLint.Scribe;

internal static class FileMapEmitter
{
    internal const string RelativePath = "Generated/FILEMAP.md";

    internal static int Emit(
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
            var manifest = FileMapLoader.LoadRepository(repositoryRoot);
            var first = FileMapProjectionWriter.Write(manifest);
            var second = FileMapProjectionWriter.Write(manifest);
            if (!first.AsSpan().SequenceEqual(second.AsSpan()))
            {
                throw new InvalidOperationException("FILEMAP projection writer is not byte deterministic.");
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
                ?? throw new InvalidOperationException("FILEMAP projection path has no parent directory.");
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
            error.WriteLine("filemap emit failed: " + exception.Message);
            return 2;
        }
    }
}
