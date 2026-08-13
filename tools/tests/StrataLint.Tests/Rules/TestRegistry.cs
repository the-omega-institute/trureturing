using System.Text;

namespace StrataLint.Tests;

internal static class TestRegistry
{
    internal const string RelativePath = "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml";

    // Declared before Canonical on purpose: static fields initialize in declaration
    // order, and LoadRepository decodes through this encoder.
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static readonly string Canonical = LoadRepository(TestRepositoryLayout.FindRoot());

    internal const string Domains = """
        domains:
          Carrier:
            stratum: S0
            definition: The golden integer carrier.
          Conventions:
            stratum: S0
            definition: Canonical W-digit conventions.
          Phase:
            stratum: S1
            definition: Additive golden-ratio phases modulo one.
          Weil:
            stratum: S3
            definition: Classical zeta conventions and Weil test functions.
        """ + "\n";


    private static string LoadRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var path = Path.Combine(repositoryRoot, RelativePath);
        if (!File.Exists(path))
        {
            throw new FileNotFoundException($"fixture registry is absent: {RelativePath}", path);
        }

        var bytes = File.ReadAllBytes(path);
        if (bytes.Length == 0
            || bytes[^1] != (byte)'\n'
            || bytes.AsSpan().Contains((byte)'\r')
            || bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble))
        {
            throw new FormatException(
                $"fixture registry must be strict UTF-8 without BOM/CR and end in LF: {RelativePath}");
        }

        try
        {
            return StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException($"fixture registry is not strict UTF-8: {RelativePath}", exception);
        }
    }

}
