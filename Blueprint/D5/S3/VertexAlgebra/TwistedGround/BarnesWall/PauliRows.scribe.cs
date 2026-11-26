using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallPauliRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ambient Pauli action at rank 128",
        H("The ambient Pauli action at rank 128"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-paulirows"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/PauliRows.defect_abs_det"),
            H("Each quaternion generator has absolute displacement determinant 2^64"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The three ambient generators act by signed permutations of the tensor coordinates. " +
                "Each generator squares to negative identity and is skew-symmetric. The displacement times " +
                "its transpose is twice the identity. Its determinant is the square of the absolute " +
                "displacement determinant."))),
            DescribeRole.Theorem))));
}
