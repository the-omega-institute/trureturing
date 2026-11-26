using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallRank128LatticeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rank-128 Barnes–Wall lattice Gram",
        H("The rank-128 Barnes–Wall lattice Gram"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-rank-128-gram"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Rank128Lattice.gram_det"),
            H("Unimodularity of the tensor Gram"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The tensor basis factors the integer Gram as a rational triangular subset-incidence matrix " +
                "times its transpose. Complementary words have reciprocal row factors, so the determinant " +
                "is one. The halved diagonal and strict lower triangle reduce to the cocycle used for the " +
                "rank-128 quaternion trace."))),
            DescribeRole.Theorem))));
}
