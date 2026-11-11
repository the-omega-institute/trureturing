using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class CollisionErrorBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionErrorBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic reduction separates distinct-shift products from sparse collision errors.",
        H("Weighted collision error bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("collision-error-bound"),
                DeclarationHandle.Create(Prefix + "collision_error_bound"),
                H("The weighted collision error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every maximum order q and real endpoint cap M at least one there is a nonnegative constant C. For N at least two, integer H at least one with MH at most N, a weight w with BVBound(w,B), any positive order k at most q, and any admissible family of k intervals in [0,M], the weighted discrete mixed moment differs from the sum of its tuple reductions at log n by at most C B times the sum of sqrt(N) H^(k-1) (log N)^(k+1) and H^k (log N)^(k-1). The first term comes from proper prime powers, counted using their square-root bound. A quadratic defect contributes only when its shift is repeated, leaving at most k-1 free shifts. The frozen theorem LongGapsBetweenPrimes.product_collision_bound is applied to the subtype of shifts in a nonempty box P, with Unit as the mark type, uniform weights 1/card(P), and the mark that a shift equals a fixed e in P. Its normalized collision estimate gives count/card(P)^k at most k squared/card(P)^2. For k at least two, clearing the positive denominator bounds the repeated-tuple count by k squared times card(P)^(k-2). Values outside P and orders below two have zero repeated-tuple count; this also covers empty boxes. At order one there are no repeated shifts, and the reduction error vanishes. Outside those exceptions the logarithm-shift bound controls the defect by MH/N times a logarithmic factor. The estimate is uniform in all interval endpoints and in the weight. Together with the common polynomial expansion of reducedAt and reducedTuple, it supplies the collision step of the weighted arithmetic transfer to Phi."))),
                DescribeRole.Theorem))));
}
