using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallQ8GroundTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quaternion trace product on the Barnes–Wall ground space",
        H("The quaternion trace product on the Barnes–Wall ground space"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-q8-actual-trace"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Q8GroundTrace.exists_quaternion_intertwiners"),
            H("The prescribed phases give concrete quaternion intertwiners"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The actual rank-128 reflection-quotient representation has dimension 2^64. The prescribed " +
                "lift phases satisfy the binary polarization identities, so the finite Weyl sum gives " +
                "intertwiners of trace 2^64. Their product has trace 2^96, giving the normalized " +
                "trace product 2^32."))),
            DescribeRole.Theorem))));
}
