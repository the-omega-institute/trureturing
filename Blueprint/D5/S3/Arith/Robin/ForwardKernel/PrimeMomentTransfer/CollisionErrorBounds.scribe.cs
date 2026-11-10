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
                    "For every real endpoint cap M at least one there is a nonnegative constant C. For N at least two, integer H at least one with MH at most N, a weight w with BVBound(w,B), k equal to two, three or four, and any admissible family of k intervals in [0,M], the weighted discrete mixed moment differs from the sum of its tuple reductions at log n by at most C B times the sum of sqrt(N) H^(k-1) (log N)^(k+1) and H^k (log N)^(k-1). The first term comes from proper prime powers, counted using their square-root bound. A quadratic defect contributes only when its shift is repeated, leaving at most k-1 free shifts. The quadratic diagonal, five cubic and fifteen fourth-order equality patterns bound this repetition sum. Outside those exceptions the logarithm-shift bound controls the defect by MH/N times a logarithmic factor. The estimate is uniform in all interval endpoints and in the weight. Together with the common polynomial expansion of reducedAt and reducedTuple, it supplies the collision step of the weighted arithmetic transfer to Phi."))),
                DescribeRole.Theorem))));
}
