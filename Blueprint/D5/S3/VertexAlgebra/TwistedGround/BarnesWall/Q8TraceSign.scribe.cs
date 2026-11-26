using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.BarnesWall;

internal sealed class BarnesWallQ8TraceSignDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Barnes–Wall quaternion trace sign",
        H("The Barnes–Wall quaternion trace sign"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-quaternion-ground-gauss-sum"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Q8TraceSign.defect_ground_gauss_sum"),
            H("Gauss sum on the common displacement image"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(
                Paragraph(Text(
                    "The rank-128 tensor basis and strict-lower-triangular lift phases give two " +
                    "displacement maps from the quaternion generators. Their images coincide and " +
                    "are spanned by the 64 even binary labels.")),
                Paragraph(Text(
                    "On the common image the trace-product exponent has a perfect cross pairing " +
                    "between the 32 coordinates on each side of the third-bit split. An involutive " +
                    "shear reduces the sign sum to 32 copies of the binary hyperbolic sum, giving " +
                    "the positive value 2^32. This is the finite trace calculation used in the " +
                    "anomaly argument for Conjecture 5.2."))),
            DescribeRole.Theorem))));
}
