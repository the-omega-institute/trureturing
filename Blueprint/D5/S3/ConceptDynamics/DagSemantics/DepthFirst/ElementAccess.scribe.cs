using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics.DepthFirst;

internal sealed class ElementAccessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ElementAccess.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/zhao2023algorithm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total indexed lookup and update",
        H("ElementAccess"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("indexed-total-update"),
                DeclarationHandle.Create(Prefix + "GetSetElemAllValid"),
                H("Total indexed lookup and update"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Original lookup and update interfaces assert index validity and the same-index and distinct-index update laws."))),
                DescribeRole.Definition),
            Paragraph(Text("The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.")))));
}
