using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CoupledAngleBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict scalar ratio bound for the mixed-matching coupled-angle estimate.",
        H("The coupled-angle ratio bound"),
        Blocks(
            Paragraph(Text(
                "Let Q, T and k be real numbers with 0<k<1, "
                + "(2-k)/k<Q and Q<=T. Define the coupled ratio as "
                + "(Q+T squared) times k divided by "
                + "2 times (T squared minus one) plus (Q+1) times k.")),
            Describe.Lean(
                DescribeId.Create("coupled-ratio-half-angle-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/CoupledAngleBound.coupled_ratio_lt_half_angle"),
                H("The ratio lies below the half-angle bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The coupled ratio is strictly less than k divided by "
                        + "2-k. The hypotheses ensure every denominator is positive.")),
                    Paragraph(Text(
                        "The proof factors the difference between the two cross-multiplied "
                        + "sides. The factor k times Q minus (2-k) is positive by the "
                        + "strict lower bound on Q, while Q+1 is positive. The assumption "
                                                + "Q<=T then transfers this strict gap from Q squared to T squared.")),
                    Paragraph(Text(
                        "This is the scalar monotonicity component of the mixed-matching "
                        + "angle estimate. It does not assert a tetrahedral realization, "
                        + "a common edge length, or a global angle equation."))),
                DescribeRole.Theorem))));
}

