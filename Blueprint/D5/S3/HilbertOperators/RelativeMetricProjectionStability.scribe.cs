using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class RelativeMetricProjectionStabilityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/HilbertOperators/RelativeMetricProjectionStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A relative operator sandwich controls the change of orthogonal projection onto one subspace.",
        H("Relative metric projection stability"),
        Blocks(
            Describe.Lean(DescribeId.Create("projection-angle"),
                DeclarationHandle.Create(Module + "opNorm_sub_starProjection_le"),
                H("Distance between the two projections"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let A be a bounded symmetric operator on a complex Hilbert space, with " +
                    "l I ≤ A ≤ u I and 0 < l ≤ u. If R fixes the visible subspace V, has range " +
                    "in V, and its residual is A-orthogonal to V, its distance from the " +
                    "ordinary orthogonal projection is at most (u − l)/(2√(ul)). " +
                    "For a unit vector w in V with Rayleigh mean m, positivity of " +
                    "(A − l I)(u I − A) bounds the squared centered residual by (u − m)(m − l). " +
                    "Completing the square bounds the residual divided by m, and orthogonality " +
                    "converts that bound into control of R on the reference orthogonal complement."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("visible-compression"),
                DeclarationHandle.Create(Module + "visibleCompression_sub_le"),
                H("Change of visible compression"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a bounded operator T, the two compressions agree on the part of T(V) " +
                    "inside V. Their difference factors through the visible-to-hidden block of T. " +
                    "Its norm is bounded by the projection-angle coefficient times the norm of that block."))),
                DescribeRole.Theorem))));
}
