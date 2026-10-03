using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Scribe;

public sealed record ScribeResourceInput(string Path, string? Sha256);

/// <summary>Repository bytes and absence observations within one script execution.</summary>
internal sealed class ScribeInputRecorder : IDisposable
{
    private static readonly AsyncLocal<ScribeInputRecorder?> Current = new();
    private readonly ScribeInputRecorder? previous;
    private readonly string root;
    private readonly Dictionary<string, byte[]?> bytes = new(StringComparer.Ordinal);
    private readonly Dictionary<string, ScribeResourceInput> observations = new(StringComparer.Ordinal);

    internal ScribeInputRecorder(string repositoryRoot)
    {
        root = System.IO.Path.GetFullPath(repositoryRoot);
        previous = Current.Value;
        Current.Value = this;
    }

    internal ImmutableArray<ScribeResourceInput> Inputs => observations.Values
        .OrderBy(input => input.Path, StringComparer.Ordinal).ToImmutableArray();

    internal static byte[]? ReadFile(string repositoryRoot, string relativePath)
    {
        var fullRoot = System.IO.Path.GetFullPath(repositoryRoot);
        var normalized = relativePath.Replace('\\', '/');
        var scope = Current.Value;
        if (scope is not null && scope.root != fullRoot)
            throw new InvalidOperationException("Script repository read differs from the execution root.");
        if (scope is not null && scope.bytes.TryGetValue(normalized, out var captured)) return captured;
        var fullPath = System.IO.Path.Combine(fullRoot, normalized.Replace('/', System.IO.Path.DirectorySeparatorChar));
        var content = File.Exists(fullPath) ? File.ReadAllBytes(fullPath) : null;
        if (scope is not null)
        {
            scope.bytes.Add(normalized, content);
            scope.Record(new ScribeResourceInput(normalized, content is null ? null : ScribeResourcePack.Digest(content)));
        }
        return content;
    }

    internal static string ReadText(string repositoryRoot, string relativePath)
    {
        var content = ReadFile(repositoryRoot, relativePath)
            ?? throw new FileNotFoundException("Script source is missing.", relativePath);
        using var reader = new StreamReader(new MemoryStream(content), Encoding.UTF8, detectEncodingFromByteOrderMarks: true);
        return reader.ReadToEnd();
    }

    internal static void Replay(ImmutableArray<ScribeResourceInput> inputs)
    {
        if (Current.Value is not { } scope) return;
        foreach (var input in inputs) scope.Record(input);
    }

    private void Record(ScribeResourceInput input)
    {
        if (observations.TryGetValue(input.Path, out var recorded) && recorded != input)
            throw new InvalidOperationException($"Repository input changed within execution: {input.Path}.");
        observations[input.Path] = input;
    }

    public void Dispose() => Current.Value = previous;
}
