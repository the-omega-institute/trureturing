using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicPadicConjugacyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A root-free coordinate conjugates multiplication by nine to the shifted cubic Lucas update on the entire small p-adic ball.",
        H("Isometric p-adic linearization of the cubic Lucas update"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubic-coordinate-summable"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicPadicConjugacy.coordinate_summable"),
                H("Convergence throughout the small ball"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The factorial valuation bound puts all coefficients of the rescaled series within a geometric norm bound. "
                    + "This proves summability for every point in the small p-adic ball at primes at least five."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-coordinate-isometric-conjugacy"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicPadicConjugacy.linearizingIsometry_conj"),
                H("The full ball conjugacy and isometry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The evaluated coordinate is an isometric bijection of the closed ball of radius one over p. "
                    + "Its inverse follows from a strict contraction of the nonlinear remainder. "
                    + "Multiplication by nine becomes the cubic map y times (y+3) squared under this bijection. "
                    + "The identity is evaluated using summability and Cauchy products, and no square root of an input is selected."))),
                DescribeRole.Theorem))));
}
