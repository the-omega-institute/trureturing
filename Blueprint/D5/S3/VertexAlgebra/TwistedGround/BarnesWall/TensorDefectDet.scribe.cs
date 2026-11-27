using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallTensorDefectDetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The order-four Pauli defect determines the twisted ground multiplicity",
        H("The order-four Pauli defect determines the twisted ground multiplicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-tensor-defect-multiplicity"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorDefectDet.groundMultiplicity_eq"),
            H("The order-four Pauli defect determines the twisted ground multiplicity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "A tensor Pauli word with odd square exponent squares to negative identity. " +
                "Its defect takes the unimodular tensor Gram to twice that Gram. " +
                "The determinant identity gives the same positive square-root dimension for each of the three quaternion words."))),
            DescribeRole.Theorem))));
}
