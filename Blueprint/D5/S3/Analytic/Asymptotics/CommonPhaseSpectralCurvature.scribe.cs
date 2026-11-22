using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class CommonPhaseSpectralCurvatureDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Analytic/Asymptotics/CommonPhaseSpectralCurvature";
    private const string Digest =
        "A divergent real second moment forces spectral curvature to diverge at a common phase.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Gid, Digest, "evidence-not-specified-by-formal-manifest"),
        H("Spectral curvature at a common phase"),
        Blocks(
            Paragraph(Text(
                "Let A, B, d, and ω be real sequences indexed by ℕ. Assume A(j) ≥ 0, "
                + "A and |B| are summable, and |d(j)| ≤ 1 for all j. Define S(h) as "
                + "−2 times the sum of exp(d(j)h)(A(j)cos(ω(j)h) − B(j)sin(ω(j)h)). "
                + "The summands inside the sum are absolutely summable for each real h, "
                + "by the majorant exp(|h|)(A(j)+|B(j)|).")),
            Describe.Lean(
                DescribeId.Create("spectral-quadratic-error"),
                DeclarationHandle.Create(Gid + ".abs_symmetric_second_difference_sub_cosine_defect_le"),
                H("A quadratic bound on the error in the cosine defect comparison"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume additionally that |B(j)ω(j)| is summable. Put "
                        + "D(h) = ∑ⱼ A(j)(1−cos(ω(j)h)) and C = ∑ⱼ (A(j)+2|B(j)ω(j)|). "
                        + "For every real h with |h| ≤ 1, "
                        + "|S(h)+S(−h)−2S(0)−4D(h)| ≤ 4h²C.")),
                    Paragraph(Text(
                        "Pairing h and −h produces the hyperbolic cosine in the real part "
                        + "and the hyperbolic sine in the imaginary part. For |x| ≤ 1, "
                        + "|cosh(x)−1| ≤ x² and |sinh(x)| ≤ 2|x|. Apply these at x = d(j)h "
                        + "and use |sin(ω(j)h)| ≤ |ω(j)h|. The error before the factor 4 "
                        + "is bounded term by term by h²(A(j)+2|B(j)ω(j)|)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("divergent-spectral-curvature"),
                DeclarationHandle.Create(Gid + ".tendsto_symmetric_second_difference_div_sq_atTop"),
                H("Divergence of the normalized spectral second difference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the hypotheses of the quadratic error estimate, assume also "
                        + "that A(j)ω(j)² is not summable. Then "
                        + "(S(h)+S(−h)−2S(0))/h² tends to +∞ as h tends to zero with h ≠ 0.")),
                    Paragraph(Text(
                        "The normalized second difference is at least 4D(h)/h²−4C for "
                        + "0 < |h| ≤ 1. The cosine second-moment theorem makes D(h)/h² "
                        + "tend to +∞ in the same punctured neighborhood."))),
                DescribeRole.Theorem))));
}
