namespace StrataLint.Scribe.Tests;

public sealed class MarkdownCheckCommandTests
{
    [Fact]
    public void ReadsTheNulSeparatedPathsAChangeHandsIt()
    {
        // `git diff -z` writes them this way, and the workflow pipes that verbatim.
        var paths = MarkdownFormulaScope.ParsePaths(
            "Blueprint/D5/S0/Second.md\0Blueprint/D5/S0/First.scribe.cs\0"
            + "Blueprint/D5/S0/Second.md\0\0 Blueprint/D5/S0/Third.md \0");

        Assert.Equal(
            [
                "Blueprint/D5/S0/First.scribe.cs",
                "Blueprint/D5/S0/Second.md",
                "Blueprint/D5/S0/Third.md",
            ],
            paths.AsEnumerable());
    }

    [Fact]
    public void ReadsNothingFromAnEmptyChange()
    {
        Assert.Empty(MarkdownFormulaScope.ParsePaths(string.Empty));
        Assert.Empty(MarkdownFormulaScope.ParsePaths("\0\0"));
    }
}
