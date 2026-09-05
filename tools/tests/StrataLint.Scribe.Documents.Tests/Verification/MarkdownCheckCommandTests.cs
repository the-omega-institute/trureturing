namespace StrataLint.Scribe.Tests;

public sealed class MarkdownCheckCommandTests
{
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

        var exit = ScribeCli.Run(DocumentAssembly.Value, arguments, temporary.Path, TextWriter.Null, error);

        Assert.Equal(2, exit);
        Assert.Contains(
            "markdown-check --report <file> --paths-from <file|->",
            error.ToString(),
            StringComparison.Ordinal);
    }
}
