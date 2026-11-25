using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeQuarterTriangleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-sided ordinary-prime sum on the quarter grid characterizes the Riemann hypothesis.",
        H("A triangular ordinary-prime criterion for RH"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-iff-eventual-prime-triangle-lower"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeQuarterTriangle.rh_iff_eventual_prime_triangle_lower"),
            H("The prime triangle on the quarter grid"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For x = k/4, sum log p over primes x < p ≤ 4x with weight "
                    + "2 − 2x/p when p ≤ 2x and 4x/p − 1 when p ≥ 2x. "
                    + "The Riemann hypothesis is equivalent to the existence of one A ≥ 0 "
                    + "for which this sum is at least 2x log 2 − A√x at every sufficiently large k.")),
                Paragraph(Text(
                    "The centered Mangoldt triangle is the difference U(4x) − 3U(2x) + 2U(x). "
                    + "All its knots lie on the quarter grid. Prime powers beyond the primes "
                    + "have nonnegative contributions and total weight O(√x). The reverse implication "
                    + "interpolates the lower bound and solves the dyadic difference inequality using "
                    + "U(x)/x → 0. This gives the one-sided Mangoldt bound at the square-root scale."))),
            DescribeRole.Theorem))));
}
