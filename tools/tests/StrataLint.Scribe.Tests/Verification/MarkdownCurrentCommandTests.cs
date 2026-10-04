
namespace StrataLint.Scribe.Tests;

public sealed class MarkdownCurrentCommandTests
{

    [Fact]
    public void CurrentChecksEveryDefinitionWithoutGitOrPublishedMarkdown()
    {
        using var temporary = Prepare();
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = Run(temporary, output, error);

        Assert.True(exit == 0, error.ToString());
        Assert.Contains("markdown: judged=1", output.ToString(), StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(temporary.Path, ".git")));
    }

    [Theory]
    [InlineData("Blueprint/D5/S0/Synthetic/CurrentMarkdown.md", "Double subscript")]
    [InlineData("Blueprint/D5/S0/Synthetic/Orphan.md", "no Scribe document renders")]
    public void CurrentRejectsInvalidPublishedMarkdownAndOrphans(string path, string diagnostic)
    {
        using var temporary = Prepare();
        TemporaryFileSystem.File.WriteAllText(temporary.Resolve(path), "# Probe\n\n$$u_{n}_{i}$$\n");
        var error = new StringWriter();

        Assert.Equal(1, Run(temporary, TextWriter.Null, error));
        Assert.Contains(diagnostic, error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void ExplicitEmptyScopeDoesNotJudgeUnselectedPublishedMarkdown()
    {
        using var temporary = Prepare();
        TemporaryFileSystem.File.WriteAllText(
            temporary.Resolve("Blueprint/D5/S0/Synthetic/CurrentMarkdown.md"), "# Probe\n\n$$u_{n}_{i}$$\n");
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = Run(temporary, output, error, "--paths-from", "-");

        Assert.True(exit == 0, error.ToString());
        Assert.Contains("markdown: judged=0", output.ToString(), StringComparison.Ordinal);
    }

    public static DocumentDefinition Definition() => DocumentDefinition.Create(
        ScribeDocument.Create(
            DefinitionDsl.Header("D5/S0/Synthetic/CurrentMarkdown", "Current Markdown command fixture."),
            DefinitionDsl.H("Current Markdown"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(
                DefinitionDsl.Text("A current formula "), DefinitionDsl.Math(FormulaDsl.Id("x")), DefinitionDsl.Text(".")))),
        "Blueprint/D5/S0/Synthetic/CurrentMarkdown.scribe.cs");

    private static TemporaryRoot Prepare()
    {
        var temporary = new TemporaryRoot();
        SyntheticScribeRepository.WriteInputs(temporary.Path, Definition());
        TemporaryFileSystem.File.WriteAllText(temporary.Resolve("global.json"), "{}\n");
        TemporaryFileSystem.File.WriteAllText(temporary.Resolve(Definition().SourcePath), $$"""
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            {{"namespace StrataLint.Scribe.Blueprint.D5.S0.Synthetic;"}}
            internal sealed class CurrentMarkdown : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
                    Header("D5/S0/Synthetic/CurrentMarkdown", "Current Markdown command fixture."), H("Current Markdown"),
                    Blocks(Paragraph(Text("A current formula "), Math(FormulaDsl.Id("x")), Text(".")))));
            }
            """);
        return temporary;
    }

    private static int Run(TemporaryRoot temporary, TextWriter output, TextWriter error, params string[] options)
    {
        var paths = options.Length == 0
            ? string.Join('\0', Directory.EnumerateFiles(temporary.Resolve("Blueprint"), "*", SearchOption.AllDirectories)
                .Select(path => System.IO.Path.GetRelativePath(temporary.Path, path).Replace('\\', '/')))
            : string.Empty;
        return ScribeCli.Run(["markdown-check", "--report", "fixture.json", "--paths-from", "-"],
            temporary.Path, output, error, LeanReportFixture.ForDocuments([Definition().Document]), new StringReader(paths));
    }

}
