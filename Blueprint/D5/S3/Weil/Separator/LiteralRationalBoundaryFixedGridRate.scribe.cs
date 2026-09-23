using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class LiteralRationalBoundaryFixedGridRateDocument
    : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Weil/Separator/LiteralRationalBoundaryFixedGridRate."
        + "fixedGridRateCertified";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal rational fixed grid has an explicit mesh-plus-scalar dyadic width rate.",
        H("Rate Certificate for a Literal Rational Fixed Grid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-grid-rate-certified"),
                DeclarationHandle.Create(Result),
                H("Explicit mesh and scalar error budgets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the exact payload built by boundaryGrid R p q k s, the theorem "
                            + "derives rational amplitude caps for all four endpoints of the "
                            + "real and imaginary integral intervals. Polynomial value and "
                            + "derivative bounds, cutoff and exponential bounds, and a "
                            + "telescoping cell estimate produce explicit constants Cmesh and "
                            + "Cscalar.")),
                    Paragraph(Text(
                        "The completed-square width is at most Cmesh/2^k plus "
                            + "Cscalar*(1/2)^s. Both the mesh error and scalar-enclosure error "
                            + "are proved for the computed signed payload; neither is accepted "
                            + "from the caller.")),
                    Paragraph(Text(
                        "This rate controls only the pole-boundary enclosure for the literal "
                            + "same-H family. It does not certify compact, prime, or Archimedean "
                            + "intervals, assert an off-line zero, extract a negative witness, "
                            + "or prove the Riemann hypothesis."))),
                DescribeRole.Theorem)),
        []));
}
