using StrataLint.EngineeringScope;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.InspectionIntegration.Tests;

public sealed class FileMapInspectionScopeTests
{
    [Theory]
    [InlineData("Blueprint/D5/Changed.md")]
    [InlineData("Generated/Changed.json")]
    [InlineData("Evidence/D5/Changed.json")]
    public void RepositoryWhitelistDoesNotExpandConsumersForAnExistingChangedPath(string changed)
    {
        var result = FileMapInspectionScope.Select(RepositoryRegistration(), [changed],
            [changed, "Data/Unchanged.json", "Meta/Unchanged.toml", "Library/Unchanged.yaml", "Blueprint/D5/Unchanged.scribe.cs"]);
        Assert.Equal(new[] { changed }, result.Paths);
        Assert.Empty(result.RelatedPatterns!);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RepositoryWhitelistInspectsRegisteredConsumersWhenAPathIsRemovedOrRenamed(bool renamed)
    {
        var changes = renamed ? new[] { "Blueprint/D5/Old.md", "Blueprint/D5/New.md" } : ["Blueprint/D5/Old.md"];
        var result = FileMapInspectionScope.Select(RepositoryRegistration(), changes,
            ["Blueprint/D5/New.md", "Data/Reference.json", "Meta/Reference.toml", "Blueprint/D5/Reference.scribe.cs", "D5/Unrelated.lean"]);
        Assert.Equal(changes.Concat(new[] { "Data/Reference.json", "Meta/Reference.toml", "Blueprint/D5/Reference.scribe.cs" })
            .Order(StringComparer.Ordinal), result.Paths);
        Assert.NotEmpty(result.RelatedPatterns!);
    }

    private static RegisteredFileMapScope RepositoryRegistration()
    {
        using var document = JsonDocument.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Meta/ci-checks.json")));
        var check = document.RootElement.GetProperty("checks").EnumerateArray().Single(row => row.GetProperty("id").GetString() == "filemap");
        return check.GetProperty("delta_scope").Deserialize<RegisteredFileMapScope>(new JsonSerializerOptions
        { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower })!;
    }
}
