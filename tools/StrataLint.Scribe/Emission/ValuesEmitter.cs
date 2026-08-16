namespace StrataLint.Scribe;

public static class ValuesEmitter
{
    public static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error)
    {
        return EmitCore(repositoryRoot, check, output, error, delta: null);
    }

    internal static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        ScribeDeltaInputs delta)
    {
        ArgumentNullException.ThrowIfNull(delta);
        if (!check)
        {
            throw new ArgumentException("Scribe delta scope is only valid for checks.", nameof(check));
        }
        return EmitCore(repositoryRoot, check, output, error, delta);
    }

    private static int EmitCore(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        ScribeDeltaInputs? delta)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);

        try
        {
            if (delta is not null
                && !ScribeDeltaScope.RequiresValuesProjection(
                    delta.Changes,
                    delta.ProducerPaths))
            {
                output.WriteLine("checked: 0 values projection(s)");
                return 0;
            }

            var first = CanonicalValuesWriter.Write(repositoryRoot).ToArray();
            var second = CanonicalValuesWriter.Write(repositoryRoot).ToArray();
            if (!first.AsSpan().SequenceEqual(second))
            {
                throw new InvalidOperationException("Values writer is not byte deterministic.");
            }

            var path = Path.Combine(repositoryRoot, CanonicalValuesWriter.RelativePath);
            var current = File.Exists(path) ? File.ReadAllBytes(path) : [];
            if (current.AsSpan().SequenceEqual(first))
            {
                output.WriteLine("checked: " + CanonicalValuesWriter.RelativePath);
                return 0;
            }

            if (check)
            {
                error.WriteLine("out of date: " + CanonicalValuesWriter.RelativePath);
                return 1;
            }

            var parent = Path.GetDirectoryName(path)
                ?? throw new InvalidOperationException("Values projection path has no parent directory.");
            Directory.CreateDirectory(parent);
            File.WriteAllBytes(path, first);
            output.WriteLine("wrote: " + CanonicalValuesWriter.RelativePath);
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
