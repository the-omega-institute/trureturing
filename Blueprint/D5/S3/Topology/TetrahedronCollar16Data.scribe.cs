using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class TetrahedronCollar16DataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The depth-three tetrahedral table",
        H("The depth-three tetrahedral table"),
        Blocks(Describe.Lean(
            DescribeId.Create("tetrahedroncollar16data-result"),
            DeclarationHandle.Create("D5/S3/Topology/TetrahedronCollar16Data.rows3"),
            H("The depth-three tetrahedral table"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Each entry encodes a nonempty flag in the third ordinary subdivision of the ordered tetrahedron and its main height or extra colour. The certificate module verifies the table against the actual flags."))),
            DescribeRole.Definition))));
}
