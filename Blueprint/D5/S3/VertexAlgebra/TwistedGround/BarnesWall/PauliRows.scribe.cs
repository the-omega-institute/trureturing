using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallPauliRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Pauli action on the Barnes–Wall tensor basis",
        H("The Pauli action on the Barnes–Wall tensor basis"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-paulirows"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/PauliRows.defect_abs_det"),
            H("Each quaternion generator has fixed-point-free defect order 2^64"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The signed coordinate permutations agree with the sparse integral rows of the tensor basis. " +
                "Each generator squares to negative identity and is skew-symmetric. The determinant " +
                "of the product of its displacement with its transpose gives the defect order."))),
            DescribeRole.Theorem))));
}
