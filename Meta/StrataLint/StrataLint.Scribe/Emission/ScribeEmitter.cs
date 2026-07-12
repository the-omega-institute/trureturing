using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class ScribeEmitter
{
    public static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error)
        => Emit(repositoryRoot, check, output, error, LeanCompiledArtifactReports.InspectRepository);

    internal static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        return Emit(repositoryRoot, check, output, error, _ => leanReport);
    }

    private static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        Func<string, LeanAxiomReport> loadLeanReport)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);
        ArgumentNullException.ThrowIfNull(loadLeanReport);

        try
        {
            return EmitVerified(
                repositoryRoot,
                check,
                output,
                error,
                loadLeanReport(repositoryRoot));
        }
        catch (Exception exception) when (
            exception is InvalidOperationException
                or IOException
                or UnauthorizedAccessException
                or ArgumentException)
        {
            error.WriteLine($"emit failed: {exception.Message}");
            return 1;
        }
    }

    private static int EmitVerified(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport)
    {
        var rendered = new List<(DocumentDefinition Definition, byte[] Bytes)>();
        foreach (var definition in DocumentDefinitions.All)
        {
            var first = CanonicalMarkdownWriter.Write(definition.Document, leanReport).ToArray();
            var second = CanonicalMarkdownWriter.Write(definition.Document, leanReport).ToArray();
            if (!first.AsSpan().SequenceEqual(second))
            {
                throw new InvalidOperationException(
                    $"Scribe rendering is not deterministic for {definition.Document.Header.Gid.Value}.");
            }

            rendered.Add((definition, first));
        }

        var differences = 0;
        var writes = 0;
        foreach (var (definition, expected) in rendered)
        {
            var path = Path.Combine(repositoryRoot, definition.RelativePath.Value);
            var current = File.Exists(path) ? File.ReadAllBytes(path) : [];
            if (current.AsSpan().SequenceEqual(expected))
            {
                continue;
            }

            if (check)
            {
                differences++;
                error.WriteLine($"out of date: {definition.RelativePath.Value}");
                continue;
            }

            var parent = Path.GetDirectoryName(path)
                ?? throw new InvalidOperationException("Blueprint path has no parent directory.");
            Directory.CreateDirectory(parent);
            File.WriteAllBytes(path, expected);
            writes++;
            output.WriteLine($"wrote: {definition.RelativePath.Value}");
        }

        if (check && differences == 0)
        {
            output.WriteLine($"checked: {DocumentDefinitions.All.Length} blueprint(s)");
        }
        else if (!check)
        {
            output.WriteLine($"emitted: {writes} changed blueprint(s)");
        }

        return differences == 0 ? 0 : 1;
    }
}
