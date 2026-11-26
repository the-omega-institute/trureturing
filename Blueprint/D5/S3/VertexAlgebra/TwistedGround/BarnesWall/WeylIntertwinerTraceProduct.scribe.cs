using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallWeylIntertwinerTraceProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace products of binary Weyl intertwiners",
        H("Trace products of binary Weyl intertwiners"),
        Blocks(Describe.Lean(
            DescribeId.Create("binary-weyl-intertwiner-trace"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/WeylIntertwinerTraceProduct.normalized_trace_mul_eq_gauss_sum"),
            H("The normalized trace product is a Gauss sum"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "Trace orthogonality gives an operator basis of the required dimension. Covariance recovers " +
                "each displacement coefficient from the identity coefficient. Phase-zero fixed vectors " +
                "force the support into the common displacement space and the two nonzero operators have " +
                "nonzero traces."))),
            DescribeRole.Theorem))));
}
