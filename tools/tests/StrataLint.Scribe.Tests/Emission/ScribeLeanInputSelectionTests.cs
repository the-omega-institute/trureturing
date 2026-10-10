namespace StrataLint.Scribe.Tests;

public sealed class ScribeLeanInputSelectionTests
{
    [Fact]
    public void LeanInputsComeFromSelectedTypedDocumentsAndTheirDeclarationReferences()
    {
        using var root = new TemporaryRoot(sdkConfiguration: true);
        File.WriteAllText(root.Resolve("global.json"), "{}\n");
        const string path = "Blueprint/D5/S0/Test/Selected.scribe.cs";
        File.WriteAllText(root.Resolve(path), """
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            internal sealed class Selected : IScribeDocumentDefinition
            {
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("Selected"), Blocks(Paragraph(Text("body"))),
                        [DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S0/Test/Referenced.result"))]));
            }
            """);
        File.WriteAllText(root.Resolve("Blueprint/D5/S0/Test/Unselected.scribe.cs"), "invalid unselected source");
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = ScribeCli.Run(["lean-inputs", "--paths-from", "-"], root.Path,
            output, error, new StringReader(path));

        Assert.True(exit == 0, error.ToString());
        Assert.Equal("D5.S0.Test.Referenced\nD5.S0.Test.Selected\n", output.ToString().Replace("\r\n", "\n", StringComparison.Ordinal));
        Assert.Empty(error.ToString());
        Assert.False(File.Exists(root.Resolve("Blueprint/D5/S0/Test/Selected.md")));
    }

    [Theory]
    [InlineData("")]
    [InlineData("docs/unrelated.md")]
    public void LeanInputsRejectEmptySelection(string paths)
    {
        using var root = new TemporaryRoot(sdkConfiguration: true);
        Directory.CreateDirectory(root.Resolve("Blueprint"));
        File.WriteAllText(root.Resolve("global.json"), "{}\n");

        Assert.NotEqual(0, ScribeCli.Run(["lean-inputs", "--paths-from", "-"], root.Path,
            TextWriter.Null, new StringWriter(), new StringReader(paths)));
    }
}
