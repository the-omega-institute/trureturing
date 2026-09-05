using System.Reflection;
using static StrataLint.TestSupport.DocumentProjectionBijectionAssertions;

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
    public void EngineAssemblyDiscoveryFailsClosedWhenNoDocumentDefinitionsExist()
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
            DocumentDefinitions.Discover(typeof(DocumentDefinitions).Assembly));

        Assert.Contains(
            "contains no Scribe document definitions",
            exception.Message,
            StringComparison.Ordinal);
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

    private sealed class MismatchedDefinition : IScribeDocumentDefinition
    {
        public DocumentDefinition Create() => DocumentDefinition.Create(
            ScribeDocument.Create(
                DefinitionDsl.Header("D5/S1/Phase/Basic", "Mismatch fixture."),
                DefinitionDsl.H("Mismatch"),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("fixture")))));
    }
}
