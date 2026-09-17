using System.Reflection;

namespace StrataLint.Scribe.Tests;

public sealed class MarkdownCurrentCommandTests
{
    private static readonly Assembly Documents = new FixtureAssembly();

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
        return temporary;
    }

    private static int Run(TemporaryRoot temporary, TextWriter output, TextWriter error, params string[] options) =>
        ScribeCli.Run(Documents, ["markdown-check", "--report", "fixture.json", .. options],
            temporary.Path, output, error, LeanReportFixture.ForDocuments([Definition().Document]), TextReader.Null);

    private sealed class FixtureAssembly : Assembly
    {
        public override Type[] GetTypes() => [typeof(CurrentMarkdownDocument)];
    }

    private sealed class CurrentMarkdownDocument : IScribeDocumentDefinition
    {
        public DocumentDefinition Create() => Definition();
    }
}
