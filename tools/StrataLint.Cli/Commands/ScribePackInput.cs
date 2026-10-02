using System.Collections.Immutable;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static class ScribePackInput
{
    internal static bool IsDigest(string? value) =>
        value is { Length: 64 } && value.All(Uri.IsHexDigit);

    internal static ImmutableArray<DocumentDefinition> ReadDefinitions(string path, string expectedDigest)
    {
        try
        {
            var pack = ScribeResourcePack.Open(path);
            if (!string.Equals(pack.Manifest.TotalSha256, expectedDigest, StringComparison.OrdinalIgnoreCase))
            {
                throw new FormatException(
                    $"scribe pack digest mismatch: expected {expectedDigest}, actual {pack.Manifest.TotalSha256}");
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
