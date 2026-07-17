using System.Text;

namespace StrataLint.Cli;

internal static class GoldenFixtureRegistryLoader
{
    internal const string RelativePath = "Golden/fixture-registry.yaml";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static string LoadRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var path = Path.Combine(repositoryRoot, RelativePath);
        if (!File.Exists(path))
        {
            throw new FileNotFoundException(
                $"golden fixture registry is absent: {RelativePath}",
                path);
        }

        var bytes = File.ReadAllBytes(path);
        if (bytes.Length == 0
            || bytes[^1] != (byte)'\n'
            || bytes.AsSpan().Contains((byte)'\r')
            || bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble))
        {
            throw new FormatException(
                $"golden fixture registry must be strict UTF-8 without BOM/CR and end in LF: {RelativePath}");
        }

        try
        {
            return StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException(
                $"golden fixture registry is not strict UTF-8: {RelativePath}",
                exception);
        }
    }
}
