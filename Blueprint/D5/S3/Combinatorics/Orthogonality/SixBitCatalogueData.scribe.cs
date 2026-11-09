using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class SixBitCatalogueDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact six-dimensional source representation and certificate.",
        H("Complete source objects and retained trust boundaries"),
        Blocks(
            Describe.Lean(DescribeId.Create("supplied-six-dimensional-data"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueData.dimensionSix"),
                H("supplied six dimensional data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The original exact masks, perpendicular masks, color values and adjoining-vector extension table are supplied proof inputs, imported without regeneration. There are 2825 catalogue entries including zero and 180800 extension entries. Their correctness is not a consequence of the array lengths."))), DescribeRole.Definition)),
        []));
}
