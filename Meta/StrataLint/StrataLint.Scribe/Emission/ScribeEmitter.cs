using StrataLint.Scribe.Definitions;

namespace StrataLint.Scribe;

public static class ScribeEmitter
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

        var differences = 0;
        var writes = 0;
        foreach (var pilot in PilotDocuments.All)
        {
            var path = Path.Combine(repositoryRoot, pilot.RelativePath.Value);
            var expected = CanonicalMarkdownWriter.Write(pilot.Document);
            var current = File.Exists(path) ? File.ReadAllBytes(path) : [];
            if (current.AsSpan().SequenceEqual(expected.AsSpan()))
            {
                continue;
            }

            if (check)
            {
                differences++;
                error.WriteLine($"out of date: {pilot.RelativePath.Value}");
                continue;
            }

            var parent = Path.GetDirectoryName(path)
                ?? throw new InvalidOperationException("Blueprint path has no parent directory.");
            Directory.CreateDirectory(parent);
            File.WriteAllBytes(path, expected.AsSpan());
            writes++;
            output.WriteLine($"wrote: {pilot.RelativePath.Value}");
        }

        if (check && differences == 0)
        {
            output.WriteLine($"checked: {PilotDocuments.All.Length} blueprint(s)");
        }
        else if (!check)
        {
            output.WriteLine($"emitted: {writes} changed blueprint(s)");
        }

        return differences == 0 ? 0 : 1;
    }
}
