using System.Text.Json;

namespace StrataLint.TestSupport;

// Synthetic restores use their owning fixture's private profile. Package caches
// come from the caller or the owning restore; missing packages stay offline.
public static class DotnetFixtureProfile
{
    public static IReadOnlyDictionary<string, string> Create(string fixtureRoot)
    {
        var packages = Environment.GetEnvironmentVariable("NUGET_PACKAGES");
        if (string.IsNullOrEmpty(packages))
        {
            // Read the owning project's one compiler-supplied package root;
            // moving the CLI profile must not move the already restored cache.
            var assets = Path.Combine(TestRepositoryLayout.FindRoot(),
                "tools/TestSupport/StrataLint.TestSupport/obj/project.assets.json");
            using var document = JsonDocument.Parse(File.ReadAllText(assets));
            packages = document.RootElement.GetProperty("project").GetProperty("restore")
                .GetProperty("packagesPath").GetString();
        }
        if (string.IsNullOrWhiteSpace(packages) || !Path.IsPathFullyQualified(packages))
            throw new InvalidDataException("fixture requires an absolute restored NuGet package root");
        var profile = Path.Combine(fixtureRoot, "build/dotnet-cli-profile");
        var config = Path.Combine(profile, ".nuget/NuGet/NuGet.Config");
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(config)!);
        TemporaryFileSystem.File.WriteAllText(config,
            "<configuration><packageSources><clear /></packageSources></configuration>\n");
        return new Dictionary<string, string>
        {
            ["DOTNET_CLI_HOME"] = profile,
            ["NUGET_PACKAGES"] = packages,
            ["DOTNET_GENERATE_ASPNET_CERTIFICATE"] = "false",
            ["DOTNET_CLI_TELEMETRY_OPTOUT"] = "1",
        };
    }
}
