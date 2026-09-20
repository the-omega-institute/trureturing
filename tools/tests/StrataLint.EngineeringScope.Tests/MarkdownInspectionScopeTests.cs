using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class MarkdownInspectionScopeTests
{
    private static RegisteredMarkdownScope Registration => new(
        ["tools/Renderer/**", "Meta/ci-checks.json"], ["Blueprint/**/*.md", "Blueprint/**/*.scribe.cs"]);

    [Fact]
    public void DeltaKeepsOnlyRegisteredEndpointsIncludingDeletedAndRenamedSources()
    {
        var selected = MarkdownInspectionScope.Select(Registration,
            ["Blueprint/D5/Old.scribe.cs", "Blueprint/D5/New.scribe.cs", "Blueprint/D5/Removed.md",
                "docs/theory/Other.md", "Blueprint/D5/New.scribe.cs"],
            ["Blueprint/D5/Unchanged.md"], ["Blueprint/**/*.md"]);

        Assert.False(selected.WholeTree);
        Assert.Equal(new[] { "Blueprint/D5/New.scribe.cs", "Blueprint/D5/Old.scribe.cs", "Blueprint/D5/Removed.md" }, selected.Paths);
    }

    [Theory]
    [InlineData("tools/Renderer/Formula.cs")]
    [InlineData("Meta/ci-checks.json")]
    public void RegisteredGlobalInputsSelectTheWholeDeclaredInventory(string changed)
    {
        var selected = MarkdownInspectionScope.Select(Registration, [changed],
            ["Blueprint/D5/Second.md", "docs/theory/Other.md", "Blueprint/D5/First.md"], ["Blueprint/**/*.md"]);

        Assert.True(selected.WholeTree);
        Assert.Equal(new[] { "Blueprint/D5/First.md", "Blueprint/D5/Second.md" }, selected.Paths);
    }

    [Fact]
    public void UnrelatedChangeDoesNotExpandTheMarkdownScope()
    {
        var selected = MarkdownInspectionScope.Select(Registration, ["Library/Book/source.md"],
            ["Blueprint/D5/Unchanged.md"], ["Blueprint/**/*.md"]);
        Assert.False(selected.WholeTree);
        Assert.Empty(selected.Paths);
    }

    [Fact]
    public void WholeCurrentNeedsNoDeltaAndUsesOnlyItsDeclaredInventory()
    {
        var selected = MarkdownInspectionScope.Select(null, null,
            ["Blueprint/D5/Current.md", "docs/theory/Other.md"], ["Blueprint/**/*.md"]);
        Assert.True(selected.WholeTree);
        Assert.Equal(new[] { "Blueprint/D5/Current.md" }, selected.Paths);
    }

    [Theory]
    [InlineData("empty")]
    [InlineData("duplicate")]
    [InlineData("invalid")]
    public void InvalidRegistrationCannotSelectWork(string defect)
    {
        var registration = Registration with { ChangedInputs = defect switch
        {
            "empty" => [], "duplicate" => ["Blueprint/**", "Blueprint/**"], _ => ["../outside/**"],
        } };
        var error = Assert.ThrowsAny<Exception>(() => MarkdownInspectionScope.Select(registration,
            ["Blueprint/D5/Changed.md"], [], ["Blueprint/**/*.md"]));
        Assert.Equal(defect == "invalid" ? "unsafe FILEMAP pattern: ../outside/**"
            : "empty or duplicate scribe-markdown path scope patterns", error.Message);
    }
}
