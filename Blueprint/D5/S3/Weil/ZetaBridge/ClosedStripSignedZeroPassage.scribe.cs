using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ClosedStripSignedZeroPassageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pass to the actual complete signed Weil zero sum using the existing "
            + "zeta zero-count summability and one uniform transform envelope.",
        H("The full signed zero sum under a closed-strip envelope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-zeta-signed-zero-passage"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ClosedStripSignedZeroPassage."
                    + "actual_zeta_signed_zero_tendsto"),
                H("Retain actual zeros, multiplicities and conjugate arguments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V_n converge pointwise to U on the full closed strip "
                        + "|Im z|<=1/2, with the same nonnegative D bounding each "
                        + "|V_n(z)| by D/(1+(Re z)^2). The complete actual zeta-zero "
                        + "series with terms m_rho V_n(gamma_rho) times the conjugate "
                        + "of V_n(conjugate gamma_rho) is summable at every n; the "
                        + "corresponding U series is summable, and the series converge.")),
                    Paragraph(Text(
                        "The actual closed-strip bound gives "
                        + "1+|gamma|^2 <= (5/4)(1+(Re gamma)^2)^2. Thus every term "
                        + "is bounded by (5D^2/4) m_rho/(1+|gamma_rho|^2). The "
                        + "existing actual ZetaSeam zero-summability theorem pays "
                        + "this majorant, and dominated convergence for series "
                        + "pays the limit. No new contour or zero-count argument "
                        + "is introduced.")),
                    Paragraph(Text(
                        "The original signed complex product is retained at every "
                        + "zero. It is not replaced by an absolute square, and no "
                        + "critical-line premise, positivity conclusion, extension "
                        + "to an arbitrary physical domain or RH claim is made."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/ZetaExplicit/ZeroSummability"))
        ]));
}
