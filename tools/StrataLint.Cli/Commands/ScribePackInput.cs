using System.Collections.Immutable;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static class ScribePackInput
{
    internal static bool IsDigest(string? value) =>
        value is { Length: 64 } && value.All(Uri.IsHexDigit);

    internal static ImmutableArray<DocumentDefinition> ReadDefinitions(
        string path, string expectedDigest, IScribeResourceFileView files)
    {
        try
        {
            var pack = ScribeResourcePack.Open(path);
            if (!string.Equals(pack.Manifest.TotalSha256, expectedDigest, StringComparison.OrdinalIgnoreCase))
            {
                throw new FormatException(
                    $"scribe pack digest mismatch: expected {expectedDigest}, actual {pack.Manifest.TotalSha256}");
            }

            var correspondence = ScribeResourceCorrespondence.Compare(pack, files);
            if (!correspondence.IsCorresponding)
            {
                var differences = correspondence.InputsChanged.Take(5).Select(difference => difference.ToString())
                    .Concat(correspondence.PackOnly.Take(5).Select(difference => difference + " (packOnly)"))
                    .Concat(correspondence.DiskOnly.Take(5).Select(difference => difference + " (diskOnly)"));
                throw new FormatException(FormattableString.Invariant(
                    $"ScribePackCorrespondenceMismatch: 该包与当前文件不对应: consistent={correspondence.ConsistentCount} inputsChanged={correspondence.InputsChanged.Length} packOnly={correspondence.PackOnly.Length} diskOnly={correspondence.DiskOnly.Length}")
                    + Environment.NewLine + string.Join(Environment.NewLine, differences));
            }

            return pack.ReadAll().ToImmutableArray();
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or FormatException or ArgumentException or InvalidOperationException)
        {
            throw new FormatException("scribe resource pack could not be read: " + exception.Message, exception);
        }
    }
}
