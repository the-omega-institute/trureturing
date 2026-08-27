using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class MarkdownFormulaScopeTests
{
    [Fact]
    public void AScribeSourceNamesTheMarkdownItProjectsAndNothingElseNamesADocument()
    {
        var scope = new MarkdownFormulaScope(
            RepositoryRootPath,
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
    public void ARealDocumentPassesTheGateThroughTheEmitter()
    {
        var root = RepositoryRootPath;
        var repository = RepositoryAccessor.Discover(
            RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound);
        var definition = DocumentDefinitions.All.First(candidate =>
            MarkdownMath.Extract(repository.ReadAllText(
                RepositoryRelativePath.Create(candidate.RelativePath.Value))).Length > 0);
        var report = LeanReportFixture.ForDocuments(
            DocumentDefinitions.All.Select(static item => item.Document));
        var output = new StringWriter();
        var error = new StringWriter();
        var scope = new MarkdownFormulaScope(root, [definition.RelativePath.Value]);

        var exit = ScribeEmitter.CheckMarkdown(root, output, error, report, scope);

        Assert.Equal(0, exit);
        Assert.Empty(error.ToString());
        Assert.Equal(1, scope.Judged);
        Assert.True(scope.Formulas > 0);
        Assert.Contains("markdown: judged=1", output.ToString(), StringComparison.Ordinal);
    }

    private static string RepositoryRootPath => RepositoryAccessor
        .Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound)
        .Root
        .FullPath;

    private static Func<KatexParser> Parser => () => KatexParser.Load(RepositoryRootPath);

    private static byte[] Utf8(string text) => new UTF8Encoding(false, true).GetBytes(text);

    private static string Markdown(string formula) =>
        $"# Probe\n\n## Abstract\n\nProbe.\n\n$${formula}$$\n";

    private static DocumentDefinition SyntheticDefinition()
    {
        var document = ScribeDocument.Create(
            DefinitionDsl.Header("D5/S0/Synthetic/MarkdownGate", "Synthetic markdown gate fixture."),
            DefinitionDsl.H("Synthetic markdown gate"),
            DefinitionDsl.Blocks(
                DefinitionDsl.Paragraph(DefinitionDsl.Text("Synthetic body."))));
        return DocumentDefinition.Create(
            document,
            "Blueprint/D5/S0/Synthetic/MarkdownGate.scribe.cs");
    }

    private sealed class TemporaryRoot : IDisposable
    {
        internal TemporaryRoot()
        {
            Path = System.IO.Path.Combine(
                System.IO.Path.GetTempPath(),
                "stratalint-markdown-gate-" + Guid.NewGuid().ToString("N"));
            TemporaryFileSystem.Directory.CreateDirectory(Path);
        }

        internal string Path { get; }

        public void Dispose() => TemporaryFileSystem.Directory.Delete(Path, recursive: true);
    }
}
