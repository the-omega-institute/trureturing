using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class CentralCocycleTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linearization at a central element in the quotient kernel",
        H("Linearization at a central element in the quotient kernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("central-cocycle-transport"),
            DeclarationHandle.Create(
                "D5/S3/HomologicalAlgebra/CentralCocycleTransport.slant_of_inflation_with_gauge"),
            H("The slant multiplier is the coboundary of the induced scalar gauge"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "At a central element killed in the quotient, all three terms of the inflated slant vanish. " +
                "The remaining multiplier is obtained by antisymmetrizing the two-cochain at that element. " +
                "Its scalar correction makes the projective action linear, and scalar differences between linear actions form a group character."))),
            DescribeRole.Theorem))));
}
