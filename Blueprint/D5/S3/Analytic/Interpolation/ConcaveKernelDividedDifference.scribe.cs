using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class ConcaveKernelDividedDifferenceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Interpolation/ConcaveKernelDividedDifference";
    private const string Digest =
        "A concave kernel compares the positive and negative parts of a second divided difference.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, Digest, "evidence-not-specified-by-formal-manifest"),
        H("Sign of a second divided difference with a localized positive part"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("concave-kernel-strict-sign"),
                DeclarationHandle.Create(Module + ".integral_mul_concave_neg_of_lobe_bound"),
                H("Strict sign of the integral against a concave kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let the integration interval have endpoints left and right. "
                        + "The integrand h is continuous from the smaller of a and left to right "
                        + "and strictly negative in the interior of the integration interval "
                        + "outside [a,b]. Let a < b < c <= right. The continuous concave kernel k "
                        + "is nonnegative on the interval and strictly positive inside it.")),
                    Paragraph(Text("Assume that the integral of the positive part of h from a to b "
                        + "is strictly smaller than the integral of minus h from b to c weighted "
                        + "by the fraction (c-t)/(c-a). Then the integral of h times k is negative. "
                        + "If b is at or to the left of the integration interval, strict negativity "
                        + "holds pointwise in the interior. Otherwise choose a point of maximum "
                        + "kernel value on the portion of [a,b] inside the integration interval. "
                        + "That value bounds the possible positive contribution. The chord from "
                        + "the same point to c gives the lower bound for k on [b,c] used to control "
                        + "the negative contribution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-divided-difference-strict-sign"),
                DeclarationHandle.Create(Module + ".three_node_slope_sub_slope_neg_of_lobe_bound"),
                H("Decreasing adjacent secant slopes at three distinct nodes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Estimation/deboor2005divideddifferences")),
                Blocks(
                    Paragraph(Text("Take three ordered distinct real nodes and a function with two "
                        + "derivatives on their closed span. Its second derivative must meet "
                        + "the continuity, sign, and weighted integral hypotheses of the "
                        + "preceding theorem with the first and last nodes as endpoints. "
                        + "The slope from the middle node to the last is strictly smaller than "
                        + "the slope from the first to the middle.")),
                    Paragraph(Text("On the span of the nodes, the tent kernel is the minimum of "
                        + "the affine function rising from zero to one on the left panel and "
                        + "the affine function falling from one to zero on the right panel. "
                        + "Integrating by parts on the two panels gives the difference of the "
                        + "adjacent secant slopes. Division by the positive span gives the "
                        + "classical second divided difference in de Boor's Peano-kernel "
                        + "representation. The weighted comparison supplies its sign.")),
                    Paragraph(Text("For the signed cutoff problem, use the strictly increasing "
                        + "normalized heat coordinate as the interpolation variable and take "
                        + "the second derivative of the selected linear combination in that "
                        + "variable. The sign comparison applies when the third node reaches "
                        + "the end of the certified negative interval. The spectral data and "
                        + "the lower and upper bounds for the integrals enter as hypotheses."))),
                DescribeRole.Theorem)))));
}
