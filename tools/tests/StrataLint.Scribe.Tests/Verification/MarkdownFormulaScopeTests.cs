using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class MarkdownFormulaScopeTests
{
    [Fact]
    public void AScribeSourceNamesTheMarkdownItProjectsAndNothingElseNamesADocument()
    {
        using var temporary = new TemporaryRoot();
        var scope = new MarkdownFormulaScope(
            temporary.Path,
            [
                "Blueprint/D5/S0/Probe.scribe.cs",
                "Blueprint/D5/S0/Other.md",
                "D5/S0/Probe.lean",
                "tools/StrataLint.Scribe/Emission/ScribeCli.cs",
            ],
            Parser);

        Assert.Equal(
            ["Blueprint/D5/S0/Other.md", "Blueprint/D5/S0/Probe.md"],
            scope.Paths.Order(StringComparer.Ordinal));
    }

    [Fact]
    public void JudgesOnlyTheDocumentsTheChangeNames()
    {
        using var temporary = new TemporaryRoot();
        var definition = SyntheticDefinition();
        var scope = new MarkdownFormulaScope(temporary.Path, ["Blueprint/D5/S0/Elsewhere.md"], Parser);

        scope.Inspect(definition, Utf8(Markdown(@"T^{*}^{k}")));
        scope.Close();

        Assert.Equal(0, scope.Judged);
        Assert.Equal(0, scope.Formulas);
        Assert.Empty(scope.Findings);
    }

    [Fact]
    public void RejectsAFormulaTheSiteCouldNotRender()
    {
        using var temporary = new TemporaryRoot();
        var definition = SyntheticDefinition();
        var scope = new MarkdownFormulaScope(temporary.Path, [definition.RelativePath.Value], Parser);

        scope.Inspect(definition, Utf8(Markdown(@"T^{*}^{k}")));
        scope.Close();

        Assert.Equal(1, scope.Judged);
        var finding = Assert.Single(scope.Findings);
        Assert.StartsWith(definition.RelativePath.Value + ":", finding, StringComparison.Ordinal);
        Assert.Contains("Double superscript", finding, StringComparison.Ordinal);
    }

    [Fact]
    public void JudgesTheCommittedProjectionAsWellAsTheCurrentRender()
    {
        using var temporary = new TemporaryRoot();
        var definition = SyntheticDefinition();
        var committed = Path.Combine(temporary.Path, definition.RelativePath.Value);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(committed)!);

        // The site publishes the committed bytes until the next `make emit`, so a stale
        // projection carrying a formula the current render no longer has is still judged.
        TemporaryFileSystem.File.WriteAllText(
            committed,
            Markdown("u_{n}_{i}"),
            new UTF8Encoding(false, true));
        var scope = new MarkdownFormulaScope(temporary.Path, [definition.RelativePath.Value], Parser);

        scope.Inspect(definition, Utf8(Markdown(@"{T^{*}}^{k}")));
        scope.Close();

        Assert.Equal(1, scope.Judged);
        Assert.Contains(
            "Double subscript",
            Assert.Single(scope.Findings),
            StringComparison.Ordinal);
    }

    [Fact]
    public void AScopedPathThatStillExistsButNoDocumentRendersIsReported()
    {
        using var temporary = new TemporaryRoot();
        var orphan = "Blueprint/D5/S0/Orphan.md";
        var path = Path.Combine(temporary.Path, orphan);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        TemporaryFileSystem.File.WriteAllText(path, Markdown("x"), new UTF8Encoding(false, true));
        var scope = new MarkdownFormulaScope(temporary.Path, [orphan], Parser);

        scope.Close();

        Assert.Contains("no Scribe document renders", Assert.Single(scope.Findings), StringComparison.Ordinal);
    }

    [Fact]
    public void ADeletedProjectionLeavesNothingToJudge()
    {
        using var temporary = new TemporaryRoot();
        var scope = new MarkdownFormulaScope(temporary.Path, ["Blueprint/D5/S0/Deleted.md"], Parser);

        scope.Close();

        Assert.Empty(scope.Findings);
    }

    [Fact]
    public void CarriesTheVerdictThroughTheEmitterOnBothSidesOfADocument()
    {
        using var temporary = new TemporaryRoot();
        var definition = SyntheticDefinition(FormulaDsl.Seq(
            FormulaDsl.Id("x"), FormulaDsl.Caret, FormulaDsl.Grp(FormulaDsl.D(2))));
        DocumentDefinition[] definitions = [definition];
        SyntheticScribeRepository.WriteInputs(temporary.Path, definition);
        SyntheticScribeRepository.WriteVendoredKatex(temporary.Path);
        var report = LeanReportFixture.ForDocuments([definition.Document]);
        var error = new StringWriter();
        Assert.Equal(
            0,
            ScribeEmitter.Emit(temporary.Path, check: false, TextWriter.Null, error, report, definitions));

        var output = new StringWriter();
        var exit = ScribeEmitter.CheckMarkdown(
            temporary.Path,
            output,
            error,
            report,
            new MarkdownFormulaScope(temporary.Path, [definition.RelativePath.Value]),
            definitions);

        Assert.Equal(0, exit);
        Assert.Contains("markdown: judged=1", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("red=0", output.ToString(), StringComparison.Ordinal);

        // The committed bytes are what the site publishes, so editing them past the
        // emitter is exactly the case the gate has to keep judging.
        TemporaryFileSystem.File.WriteAllText(
            Path.Combine(temporary.Path, definition.RelativePath.Value),
            Markdown("u_{n}_{i}"),
            new UTF8Encoding(false, true));
        var second = new StringWriter();
        var redError = new StringWriter();

        var redExit = ScribeEmitter.CheckMarkdown(
            temporary.Path,
            second,
            redError,
            report,
            new MarkdownFormulaScope(temporary.Path, [definition.RelativePath.Value]),
            definitions);

        Assert.Equal(1, redExit);
        Assert.Contains("markdown red", redError.ToString(), StringComparison.Ordinal);
        Assert.Contains("Double subscript", redError.ToString(), StringComparison.Ordinal);
    }

    /// <summary>A parser built from a copy of the vendored bytes under a throwaway root.</summary>
    private static Func<KatexParser> Parser
    {
        get
        {
            var temporary = new TemporaryRoot();
            SyntheticScribeRepository.WriteVendoredKatex(temporary.Path);
            return () => KatexParser.Load(temporary.Path);
        }
    }

    private static byte[] Utf8(string text) => new UTF8Encoding(false, true).GetBytes(text);

    private static string Markdown(string formula) =>
        $"# Probe\n\n## Abstract\n\nProbe.\n\n$${formula}$$\n";

    private static DocumentDefinition SyntheticDefinition(Formula? statement = null)
    {
        var body = statement is null
            ? DefinitionDsl.Paragraph(DefinitionDsl.Text("Synthetic body."))
            : DefinitionDsl.Paragraph(
                DefinitionDsl.Text("Synthetic body with "),
                DefinitionDsl.Math(statement),
                DefinitionDsl.Text("."));
        var document = ScribeDocument.Create(
            DefinitionDsl.Header("D5/S0/Synthetic/MarkdownGate", "Synthetic markdown gate fixture."),
            DefinitionDsl.H("Synthetic markdown gate"),
            DefinitionDsl.Blocks(body));
        return DocumentDefinition.Create(
            document,
            "Blueprint/D5/S0/Synthetic/MarkdownGate.scribe.cs");
    }
}
