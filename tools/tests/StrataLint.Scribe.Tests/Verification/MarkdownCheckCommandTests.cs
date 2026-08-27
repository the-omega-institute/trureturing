namespace StrataLint.Scribe.Tests;

public sealed class MarkdownCheckCommandTests
{
    [Fact]
    public void JudgesThePathsItReadsFromStandardInput()
    {
        var repository = RepositoryAccessor.Discover(
            RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound);
        var definition = DocumentDefinitions.All.First(candidate =>
            MarkdownMath.Extract(repository.ReadAllText(
                RepositoryRelativePath.Create(candidate.RelativePath.Value))).Length > 0);
        var output = new StringWriter();
        var error = new StringWriter();

        // NUL-separated, as `git diff -z` writes them and the workflow pipes them in.
        var exit = ScribeCli.Run(
            ["markdown-check", "--report", "unused", "--paths-from", "-"],
            repository.Root.FullPath,
            output,
            error,
            LeanReportFixture.ForDocuments(
                DocumentDefinitions.All.Select(static item => item.Document)),
            new StringReader(definition.RelativePath.Value + "\0"));

        Assert.Equal(0, exit);
        Assert.Empty(error.ToString());
        Assert.Contains("markdown: judged=1", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("red=0", output.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("markdown-check")]
    [InlineData("markdown-check", "--report", "report.json")]
    [InlineData("markdown-check", "--report", "report.json", "--paths-from")]
    [InlineData("markdown-check", "--paths-from", "-", "--report", "report.json")]
    [InlineData("markdown-check", "--report", "", "--paths-from", "-")]
    public void RefusesAnIncompleteInvocationWithTheUsageLine(params string[] arguments)
    {
        var error = new StringWriter();

        var exit = ScribeCli.Run(
            arguments,
            RepositoryAccessor
                .Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound)
                .Root
                .FullPath,
            TextWriter.Null,
            error);

        Assert.Equal(2, exit);
        Assert.Contains(
            "markdown-check --report <file> --paths-from <file|->",
            error.ToString(),
            StringComparison.Ordinal);
    }
}
