using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class FileMapInspectionScopeTests
{
    private static RegisteredFileMapScope Registration => new(
        ["Meta/FILEMAP*.toml", "tools/checker/**"], ["tools/**/*.cs"],
        [new(["Generated/**"], ["Data/**/*.json"], "changed")], ["tools/producers/**"]);

    [Fact]
    public void ProducerInputsInspectAllInventoryWithoutReadingUnchangedBodies()
    {
        var result = FileMapInspectionScope.Select(Registration, ["tools/producers/Writer.cs"],
            ["tools/producers/Writer.cs", "Data/old.json", "Generated/old.json"]);
        Assert.True(result.Inventory);
        Assert.Equal(new[] { "tools/producers/Writer.cs" }, result.Paths);
    }

    [Fact]
    public void OrdinaryChangeKeepsOnlyExplicitDeltaIncludingDeletedEndpoint()
    {
        var result = FileMapInspectionScope.Select(Registration,
            ["Data/changed.json", "Data/deleted.json"], ["Data/changed.json", "Data/other.json"]);
        Assert.Equal(new[] { "Data/changed.json", "Data/deleted.json" }, result.Paths);
        Assert.False(result.Actors);
    }

    [Fact]
    public void RelatedScopesUseOnlyDeclaredPatterns()
    {
        var result = FileMapInspectionScope.Select(Registration, ["Generated/removed.json"],
            ["Data/old.json", "Elsewhere/old.json", "Main.lean"]);
        Assert.Equal(new[] { "Data/old.json", "Generated/removed.json" }, result.Paths);
        Assert.False(result.Actors);
    }

    [Fact]
    public void ChangedTriggerStillInspectsRegisteredConsumersForAnExistingPath()
    {
        var result = FileMapInspectionScope.Select(Registration, ["Generated/Existing.json"],
            ["Generated/Existing.json", "Data/Reference.json", "Elsewhere/Unrelated.json"]);
        Assert.Equal(new[] { "Data/Reference.json", "Generated/Existing.json" }, result.Paths);
    }

    [Theory]
    [InlineData("Meta/FILEMAP.toml")]
    [InlineData("tools/checker/Policy.cs")]
    public void RegisteredPolicyInputsSelectWholeTree(string path)
    {
        var result = FileMapInspectionScope.Select(Registration, [path], [path, "Data/old.json"]);
        Assert.Null(result.Paths);
        Assert.True(result.Actors);
    }

    [Fact]
    public void ActorChangeDoesNotExpandDataBodies()
    {
        var result = FileMapInspectionScope.Select(Registration, ["tools/Actor.cs"], ["tools/Actor.cs", "Data/old.json"]);
        Assert.Equal(new[] { "tools/Actor.cs" }, result.Paths);
        Assert.True(result.Actors);
    }

    [Fact]
    public void MissingRegistrationCannotTurnExplicitDeltaIntoFullOrEmptyWork()
    {
        var error = Assert.Throws<InvalidDataException>(() => FileMapInspectionScope.Select(null, ["Data/changed.json"], []));
        Assert.Equal("missing filemap delta scope registration", error.Message);
    }

    [Fact]
    public void ExplicitWholeTreeInvocationRemainsAvailable()
    {
        Assert.Equal(new FileMapInspectionScope(null, true), FileMapInspectionScope.Select(null, null, []));
    }

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

    [Theory]
    [InlineData(null)]
    [InlineData("semantic")]
    public void MissingOrUnknownRelatedTriggerFailsInsteadOfGuessingScope(string? trigger)
    {
        var raw = JsonSerializer.Serialize(new { whole_tree_inputs = new[] { "Meta/FILEMAP.toml" },
            actor_inputs = new[] { "tools/**/*.cs" }, inventory_inputs = new[] { "Blueprint/**/*.scribe.cs" },
            related = new[] { new { inputs = new[] { "Generated/**" }, paths = new[] { "Data/**/*.json" }, trigger } } });
        var registration = JsonSerializer.Deserialize<RegisteredFileMapScope>(raw, new JsonSerializerOptions
        { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower });
        var error = Assert.Throws<InvalidDataException>(() => FileMapInspectionScope.Select(registration,
            ["Generated/Existing.json"], ["Generated/Existing.json", "Data/Unrelated.json"]));
        Assert.Equal("invalid filemap related trigger: expected changed or removed", error.Message);
    }

    private static RegisteredFileMapScope RepositoryRegistration()
    {
        using var document = JsonDocument.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Meta/ci-checks.json")));
        var check = document.RootElement.GetProperty("checks").EnumerateArray().Single(row => row.GetProperty("id").GetString() == "filemap");
        return check.GetProperty("delta_scope").Deserialize<RegisteredFileMapScope>(new JsonSerializerOptions
        { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower })!;
    }
}
