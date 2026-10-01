using System.Collections.Immutable;
using StrataLint.Engine;
using StrataLint.Scribe;
using StrataLint.Scribe.Documents;
using Xunit;

namespace StrataLint.Scribe.Documents.Tests.Resources;

public sealed class ScribeResourceCorpusTests
{
    [Fact]
    public void EveryDocumentDefinitionSurvivesResourceRoundTrip()
    {
        var catalog = FixtureCatalog(DocumentAssembly.Definitions.Select(static item => item.Document));
        var citations = DocumentAssembly.Definitions
            .SelectMany(static item => LiteratureReferences(item.Document))
            .DistinctBy(static item => item.BibKey.Value, StringComparer.Ordinal)
            .ToDictionary(
                static item => item.BibKey.Value,
                static _ => LiteratureCitation.Create("Fixture Authors", 2020, "Fixture citation", "10.1000/fixture"),
                StringComparer.Ordinal);
        var failures = new List<string>();
        var totalBytes = 0L;
        var sizes = new List<int>();

        foreach (var definition in DocumentAssembly.Definitions)
        {
            try
            {
                var encoded = ScribeResourceCodec.Encode(definition);
                var decoded = ScribeResourceCodec.Decode(
                    encoded,
                    expectedGid: definition.Document.Header.Gid.Value,
                    expectedSourcePath: definition.SourcePath);
                totalBytes += encoded.Length;
                sizes.Add(encoded.Length);
                Assert.Equal(encoded, ScribeResourceCodec.Encode(decoded));
                var expectedMarkdown = CanonicalMarkdownWriter.Write(definition.Document, catalog, citations);
                var actualMarkdown = CanonicalMarkdownWriter.Write(decoded.Document, catalog, citations);
                if (!expectedMarkdown.SequenceEqual(actualMarkdown))
                {
                    var difference = Enumerable.Range(0, Math.Min(expectedMarkdown.Length, actualMarkdown.Length))
                        .FirstOrDefault(index => expectedMarkdown[index] != actualMarkdown[index], -1);
                    throw new InvalidOperationException($"Markdown differs at {difference}; lengths {expectedMarkdown.Length}/{actualMarkdown.Length}.");
                }
                Assert.Equal(
                    DocumentGraphAssembler.Extract(definition.Document).Select(DocumentGraphAssembler.CanonicalKey),
                    DocumentGraphAssembler.Extract(decoded.Document).Select(DocumentGraphAssembler.CanonicalKey));
            }
            catch (Exception exception)
            {
                failures.Add($"{definition.Document.Header.Gid.Value}: {exception.GetType().Name}: {exception.Message}");
            }
        }

        Assert.True(
            failures.Count == 0,
            $"Resource round-trip failures ({failures.Count}):{Environment.NewLine}{string.Join(Environment.NewLine, failures.Take(8))}");
        Assert.NotEmpty(sizes);
        _ = totalBytes;
    }

    private static DeclarationCatalog FixtureCatalog(IEnumerable<ScribeDocument> documents)
    {
        var declarations = documents
            .SelectMany(References)
            .DistinctBy(static item => item.Reference.Value, StringComparer.Ordinal)
            .GroupBy(static item => item.Reference.Reference.Path.Value, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => new LeanFileReport(
                    [],
                    group.Select(static item => new LeanDeclaration(
                        item.Reference.Value.Replace('/', '.'),
                        item.Kind,
                        "True",
                        ["propext", "Classical.choice", "Quot.sound"]))
                        .ToImmutableArray()),
                StringComparer.Ordinal);
        return DeclarationCatalog.Create(LeanAxiomReport.Create(declarations));
    }

    private static IEnumerable<(LeanDeclarationRef Reference, string Kind)> References(ScribeDocument document) =>
        References(document.Content);

    private static IEnumerable<LibraryNoteRef> LiteratureReferences(ScribeDocument document) =>
        LiteratureReferences(document.Content);

    private static IEnumerable<LibraryNoteRef> LiteratureReferences(BlockSequence content)
    {
        foreach (var block in content.Items)
        {
            switch (block)
            {
                case DocumentBlock.Section section:
                    foreach (var item in LiteratureReferences(section.Content)) yield return item;
                    break;
                case DocumentBlock.Describe describe:
                    foreach (var item in describe.AcknowledgementReferences) yield return item;
                    if (describe.LiteratureReference is { } literature) yield return literature;
                    foreach (var item in LiteratureReferences(describe.Content)) yield return item;
                    break;
            }
        }
    }

    private static IEnumerable<(LeanDeclarationRef Reference, string Kind)> References(BlockSequence content)
    {
        foreach (var block in content.Items)
        {
            switch (block)
            {
                case DocumentBlock.Section section:
                    foreach (var item in References(section.Content)) yield return item;
                    break;
                case DocumentBlock.Describe describe:
                    if (describe.Statement is DescribeStatement.LeanDeclaration lean)
                    {
                        yield return (lean.Value, describe.KindSource is DescribeKindSource.Authored authored
                            && authored.Value is DescribeKind.Definition ? "def" : "theorem");
                    }
                    foreach (var item in References(describe.Content)) yield return item;
                    break;
            }
        }
    }
}
