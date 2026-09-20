using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class FileMapInspectionScopeTests
{
    private static RegisteredFileMapScope Registration => new(
        ["Meta/FILEMAP*.toml", "tools/checker/**"], ["tools/**/*.cs"],
        [new(["Generated/**"], ["Data/**/*.json"])], ["tools/producers/**"]);

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
}
