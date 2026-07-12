using System.Reflection;
using StrataLint.Cli;

namespace StrataLint.Scribe.Tests;

public sealed class DocumentDiscoveryTests
{
    [Fact]
    public void DiscoveryFindsEveryDefinitionInCanonicalPathOrder()
    {
        Assert.Equal(
            [
                "D5/S1/Digit/Carry",
                "D5/S1/Digit/Raw",
                "D5/S1/Phase/Basic",
                "D5/S1/Scale/Embedding",
                "D5/S1/Scale/Log",
            ],
            DocumentDefinitions.All.Select(static item => item.Document.Header.Gid.Value));
        Assert.Equal(
            [
                "Blueprint/D5/S1/Digit/Carry.md",
                "Blueprint/D5/S1/Digit/Raw.md",
                "Blueprint/D5/S1/Phase/Basic.md",
                "Blueprint/D5/S1/Scale/Embedding.md",
                "Blueprint/D5/S1/Scale/Log.md",
            ],
            DocumentDefinitions.All.Select(static item => item.RelativePath.Value));
    }

    [Fact]
    public void ReflectionDiscoveryIsDeterministic()
    {
        var assembly = typeof(DocumentDefinitions).Assembly;

        var first = DocumentDefinitions.Discover(assembly);
        var second = DocumentDefinitions.Discover(assembly);

        Assert.Equal(
            first.Select(static item => (item.Document.Header.Gid.Value, item.SourcePath)),
            second.Select(static item => (item.Document.Header.Gid.Value, item.SourcePath)));
    }

    [Fact]
    public void DiscoveryRejectsDefinitionWhoseGidDoesNotMatchItsSourcePath()
    {
        var exception = Assert.Throws<InvalidOperationException>(
            () => DocumentDefinitions.Discover(Assembly.GetExecutingAssembly()));

        Assert.Contains("D5/S1/Phase/Basic", exception.Message, StringComparison.Ordinal);
        Assert.Contains(
            "Blueprint/D5/S1/Phase/Basic.scribe.cs",
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void GeneratedMarkdownIsDeterministicAndMatchesTheCommittedTree()
    {
        var repositoryRoot = FindRepositoryRoot();
        var rootOlean = Path.Combine(
            repositoryRoot,
            ".lake",
            "build",
            "lib",
            "lean",
            "Trureturing.olean");
        if (!File.Exists(rootOlean))
        {
            var error = new StringWriter();
            var exit = ScribeEmitter.Emit(
                repositoryRoot,
                check: true,
                TextWriter.Null,
                error);

            Assert.Equal(1, exit);
            Assert.Contains("lake build", error.ToString(), StringComparison.Ordinal);
            return;
        }

        var report = LeanCompiledArtifactReports.InspectRepository(repositoryRoot);

        foreach (var definition in DocumentDefinitions.All)
        {
            var first = CanonicalMarkdownWriter.Write(definition.Document, report);
            var second = CanonicalMarkdownWriter.Write(definition.Document, report);
            var committed = File.ReadAllBytes(
                Path.Combine(repositoryRoot, definition.RelativePath.Value));

            Assert.Equal(first.ToArray(), second.ToArray());
            Assert.Equal(committed, first.ToArray());
        }
    }

    [Fact]
    public void DigitRawContainsAnHonestlyLabeledComputedZeckendorfExample()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Digit/Raw");
        var report = LeanReportFixture.ForDocuments([definition.Document]);

        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());

        Assert.Contains(
            "Z(89) + Z(34) = Z(123) = 1010000000_W",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            DeterministicComputation.ProvenanceMarker,
            markdown,
            StringComparison.Ordinal);
    }

    [Fact]
    public void PhaseBasicRendersTheCompiledInjectivityStatement()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Phase/Basic");
        var statement = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.RenderedStatement>()
            .Single();

        Assert.Equal(
            "D5/S1/Phase/Basic.goldenPhase_injective",
            statement.Declaration.Value);
        Assert.Equal(LeanDeclarationKind.Theorem, statement.Declaration.ExpectedKind);
        Assert.True(statement.Declaration.RequireNoSorry);
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "global.json"))
                && Directory.Exists(Path.Combine(current.FullName, "Blueprint")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate the repository root.");
    }

    private static IEnumerable<DocumentBlock> Descendants(BlockSequence content)
    {
        foreach (var block in content.Items)
        {
            yield return block;
            var nested = block switch
            {
                DocumentBlock.Section section => section.Content,
                DocumentBlock.Proposition proposition => proposition.Content,
                DocumentBlock.Theorem theorem => theorem.Content,
                _ => null,
            };
            if (nested is null) continue;
            foreach (var descendant in Descendants(nested)) yield return descendant;
        }
    }

    private sealed class MismatchedDefinition : IScribeDocumentDefinition
    {
        public DocumentDefinition Create() => DocumentDefinition.Create(
            ScribeDocument.Create(
                DefinitionDsl.Header("D5/S1/Phase/Basic", "Mismatch fixture."),
                DefinitionDsl.H("Mismatch"),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("fixture")))));
    }
}
