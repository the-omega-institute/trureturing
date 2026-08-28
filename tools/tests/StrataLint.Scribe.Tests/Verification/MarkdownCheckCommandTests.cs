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

    [Theory]
    [InlineData("markdown-check")]
    [InlineData("markdown-check", "--report", "report.json")]
    [InlineData("markdown-check", "--report", "report.json", "--paths-from")]
    [InlineData("markdown-check", "--paths-from", "-", "--report", "report.json")]
    [InlineData("markdown-check", "--report", "", "--paths-from", "-")]
    public void RefusesAnIncompleteInvocationWithTheUsageLine(params string[] arguments)
    {
        // The arguments are judged before any root is resolved, so a throwaway working
        // directory is all this needs.
        using var temporary = new TemporaryRoot();
        var error = new StringWriter();

        var exit = ScribeCli.Run(arguments, temporary.Path, TextWriter.Null, error);

        Assert.Equal(2, exit);
        Assert.Contains(
            "markdown-check --report <file> --paths-from <file|->",
            error.ToString(),
            StringComparison.Ordinal);
    }
}
