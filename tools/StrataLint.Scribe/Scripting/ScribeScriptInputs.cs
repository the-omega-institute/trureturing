using System.Text;

namespace StrataLint.Scribe;

/// <summary>
/// Compatibility of script-produced resource bytes. Authors increment ResourceSemanticVersion in
/// the same PR whenever DSL, factory or codec changes alter the bytes produced by an unchanged
/// script. Changes that preserve those bytes do not increment it.
/// </summary>
public static class ScribeScriptSemantics
{
    public const int ResourceSemanticVersion = 1;
}

internal static class ScribeScriptInputs
{
    // The preimage contains a little-endian integer version, length-prefixed entry bytes and
    // the ordinal path-sorted shared closure as length-prefixed UTF-8 paths and file bytes.
    internal static (string? Key, ScribeScriptFailure? Failure) Read(string root, string entry, int semanticVersion)
    {
        try
        {
            var graph = ScribeScriptHost.ReadSourceGraph(root, entry);
            if (graph.Failure is not null) return (null, graph.Failure);
            using var buffer = new MemoryStream();
            using var writer = new BinaryWriter(buffer, Encoding.UTF8, leaveOpen: true);
            writer.Write(semanticVersion);
            void Bytes(byte[] bytes)
            {
                writer.Write(bytes.Length);
                writer.Write(bytes);
            }
            byte[] Source(string path) => File.ReadAllBytes(Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar)));
            Bytes(Source(entry));
            foreach (var shared in graph.Sources!.Value.Where(path => path != entry).Order(StringComparer.Ordinal))
            {
                Bytes(Encoding.UTF8.GetBytes(shared));
                Bytes(Source(shared));
            }
            writer.Flush();
            return (ScribeResourcePack.Digest(buffer.ToArray()), null);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            return (null, new ScribeScriptFailure(ScribeScriptFailureCode.SourceRead, entry, exception.Message));
        }
    }
}
