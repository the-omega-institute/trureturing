using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class ReciprocalMoebiusFloorInverseDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaPntBounds/ReciprocalMoebiusFloorInverse";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite reciprocal Möbius floor inverse",
        H("The finite reciprocal Möbius floor inverse"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-floor-inverse"),
            DeclarationHandle.Create(Owner + ".floorIntegral_eq"),
            H("Exact finite floor integral"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Write Q(u) for the sum of μ(n)/n over positive integers n ≤ u. "
                    + "For real cutoffs P ≥ 1 and 0 ≤ x ≤ P, the integral of Q(u) times "
                    + "⌊x/u⌋ over 1 ≤ u ≤ P is max(x − 1, 0). The identity includes P = 1 "
                    + "and the range x < 1.")),
                Paragraph(Text(
                    "Expand Q as a finite sum of cutoff indicators. In the term indexed by n, "
                    + "substitute u = n v to cancel the factor 1/n. The transformed terms "
                    + "can all be integrated to P because their added tails vanish. The Möbius "
                    + "floor cancellation turns the resulting integrand into the indicator "
                    + "of v ≤ x, whose integral gives the truncated linear function."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound"))
        ]));
}
