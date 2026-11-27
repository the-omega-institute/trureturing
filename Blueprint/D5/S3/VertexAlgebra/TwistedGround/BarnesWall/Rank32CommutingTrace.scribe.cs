using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallRank32CommutingTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rank-32 commuting trace sum",
        H("The rank-32 commuting trace sum"),
        Blocks(Describe.Lean(
            DescribeId.Create("rank-32-commuting-gauss-sum"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Rank32CommutingTrace.normalized_tensor_trace_mul"),
            H("The normalized product trace of the commuting rotations is 4096"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The two rotations in distinct tensor slots have a common even displacement space. " +
                "Their literal lift exponent has four independent blocks after a parity and spectator split. " +
                "Each block pairs the sum of two coordinates with the sum of two coordinates on the other half, and its character sum is eight. " +
                "The product is 4096. With the two individual ground traces normalized to 256, this gives the reflection-ground trace used in the weight-one argument for a suitable choice of discrete torsion."))),
            DescribeRole.Theorem))));
}
