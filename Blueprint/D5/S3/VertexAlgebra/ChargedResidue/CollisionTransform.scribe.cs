using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class CollisionTransformDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supported creation diagonals of the finite physical collision transform.",
        H("Physical Binomial Collision Transform"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-collision-transform-native"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/CollisionTransform.chargedPhysicalCollisionRow_transform_native"),
                H("The physical binomial factor shifts the collision exponent by the full signed lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For every lattice, both charges, every signed gamma, delta, r, n, natural l, "
                    + "and K at least natAbs(bilinear sigma tau), the finite collision transform on each actual pure "
                    + "tensor is a quarter sum of four transformedCollisionKernel values with their projected signs. "
                    + "No positive rank, nonzero charge or positive cutoff is required.")),
                    Paragraph(Text("Each reflected pair uses its own degree N=-(r+l)-1-bilinear(c,d). A negative degree "
                    + "makes that entire component zero. Otherwise the outer range is padded down to N+1 using actual "
                    + "negative-degree vanishing. The pairTranslation support is unchanged throughout this finite sum. "
                    + "For each supported exponent t and reflected charges c,d, every summand has the same signed creation total "
                    + "-2*(r+n)-gamma-delta-4+chargeNorm(c)+chargeNorm(d)+t(0)+t(1). Negative totals vanish; "
                    + "nonnegative totals have exactly the creation range 0 through total.")),
                    Paragraph(Text("PowerSeries.binomialSeries_add and its finite coefficient convolution move gamma "
                    + "into collisionScalar(m-t(0)-chargeNorm(c)+gamma,bilinear(c,d),N). Actual ground-action multiplication "
                    + "puts the result in the common ordered ground tensor with the exact normalization "
                    + "chargeScalar(c)*chargeScalar(d)*2^(-2*bilinear(c,d)), using one cocycle. This computes the collision "
                    + "side of the desired telescope. Equality with the difference of the two ordered native kernels "
                    + "is a separate, unproved coefficient identity."))),
                DescribeRole.Theorem))));
}
