using StrataLint.Cli;

namespace StrataLint.Tests;

internal static class TestRegistry
{
    internal static readonly string Canonical =
        GoldenFixtureRegistryLoader.LoadRepository(FindRepositoryRoot());

    internal const string Domains = GoldenCorpus.FixtureDomains;

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, GoldenFixtureRegistryLoader.RelativePath)))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
