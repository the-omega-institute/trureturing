using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class LiteralRationalBoundaryFixedGridDocument
    : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGrid."
        + "fixedGridSemanticCertified";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every computed fixed grid for the literal same-H family is checker-valid and "
            + "semantically encloses its half-line pole-boundary integral.",
        H("Semantic Certificate for a Literal Rational Fixed Grid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-grid-semantic-certified"),
                DeclarationHandle.Create(Result),
                H("The computed fixed grid encloses the exact half-line integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive natural radius R and arbitrary rational p, q and dyadic "
                            + "depths, the theorem consumes exactly boundaryGrid R p q k s. "
                            + "Every cell expression and the final expression pass their "
                            + "checkers, and the assembled payload is valid.")),
                    Paragraph(Text(
                        "The real and imaginary rational intervals enclose the half-line "
                            + "integral of the literal function smoothTransition(2-|x|/R) "
                            + "times rationalEvenPolynomial p q x. Signed four-corner interval "
                            + "multiplication is retained throughout, and completed squaring "
                            + "uses the explicit positive, negative, and zero-crossing branches. "
                            + "The resulting interval encloses twice the complex norm square.")),
                    Paragraph(Text(
                        "This fixed-grid theorem does not choose a precision depth or prove a "
                            + "full-line identity. It does not certify compact, prime, or "
                            + "Archimedean intervals, assert an off-line zero, extract a negative "
                            + "witness, or prove the Riemann hypothesis."))),
                DescribeRole.Theorem)),
        []));
}
