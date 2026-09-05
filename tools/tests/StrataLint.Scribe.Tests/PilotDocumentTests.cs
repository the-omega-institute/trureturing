using System.Collections.Immutable;
using System.Reflection;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe.Tests;

public sealed class DocumentDiscoveryTests
{
    private const string PhaseSourcePath = "Blueprint/D5/S1/Phase/Basic.scribe.cs";

    [Fact]
    public void EmptyProjectionAssertionPreservesTheCompleteRepairMessage()
    {
        const string missing = "Blueprint/D5/S9/Synthetic/Missing.md";
        var findings = MarkdownProjectionBijectionFindings([missing], []);

        var exception = Record.Exception(() => AssertNoMarkdownProjectionBijectionFindings(findings));

        Assert.NotNull(exception);
        Assert.Contains(missing, exception.Message, StringComparison.Ordinal);
        Assert.Contains("run make emit and commit", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DiscoveryRejectsDefinitionWhoseGidDoesNotMatchItsSourcePath()
    {
        var exception = Assert.Throws<InvalidOperationException>(
            () => DocumentDefinitions.Discover(Assembly.GetExecutingAssembly()));

        Assert.Contains("D5/S1/Phase/Basic", exception.Message, StringComparison.Ordinal);
        Assert.Contains(
            PhaseSourcePath,
            exception.Message,
            StringComparison.Ordinal);
    }

    private static string[] MarkdownProjectionBijectionFindings(
        IEnumerable<string> requiredPaths,
        IEnumerable<string> actualPaths)
    {
        var required = requiredPaths.ToHashSet(StringComparer.Ordinal);
        var actual = actualPaths.ToHashSet(StringComparer.Ordinal);
        return required
            .Except(actual, StringComparer.Ordinal)
            .Select(static path => $"required Markdown projection is missing: {path}; "
                + $"run make emit and commit {path}")
            .Concat(actual
                .Except(required, StringComparer.Ordinal)
                .Select(static path => $"Markdown projection has no Scribe definition: {path}"))
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    private static void AssertNoMarkdownProjectionBijectionFindings(
        IReadOnlyCollection<string> findings)
    {
        var completeMessage = string.Join(" | ", findings);
        Assert.True(findings.Count == 0, completeMessage);
    }

    private static IEnumerable<DocumentBlock> Descendants(BlockSequence content)
    {
        foreach (var block in content.Items)
        {
            yield return block;
            var nested = block switch
            {
                DocumentBlock.Section section => section.Content,
                DocumentBlock.Describe describe => describe.Content,
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
