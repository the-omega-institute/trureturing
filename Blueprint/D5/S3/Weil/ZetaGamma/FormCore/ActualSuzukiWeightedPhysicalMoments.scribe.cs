using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualSuzukiWeightedPhysicalMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both literal physical moment products have L1 domains and squared bounds "
            + "controlled by the same excess integral of the original H6 source U.",
        H("Weighted physical trace and logarithmic moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-h6-weighted-physical-moments"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiWeightedPhysicalMoments."
                    + "actual_h6_weighted_physical_moments"),
            H("Actual product domains and two bounds on the same U"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source theorem quantifies over every U: R -> C and every "
                        + "hU: originalPhysicalH6 U. Explicitly, U belongs to L2 for "
                        + "Lebesgue measure restricted to x>pi, and the real density "
                        + "(x/pi)^6*norm(U(x))^2 is integrable for that same measure. "
                        + "All conclusions concern this original U and the strict "
                        + "physical half-line x>pi.")),
                Paragraph(Text(
                    "Both complex products (x^(5/4)-pi^(5/4))*U(x) and "
                        + "log(x/pi)*U(x) are Bochner integrable on x>pi. Write T(U) "
                        + "and L(U) for their literal integrals on that domain, and "
                        + "D(U)=integral_{x>pi}((x/pi)^6-1)*norm(U(x))^2. Then "
                        + "norm(T(U))^2 <= (3/40)*pi^(7/2)*D(U), and "
                        + "norm(L(U))^2 <= (3/160)*pi*D(U). The same literal D(U) "
                        + "appears in both estimates. Its density is integrable by "
                        + "subtracting the L2 density from the integrable sixth-moment "
                        + "density, and it is nonnegative on the stated strict domain.")),
                Paragraph(Text(
                    "The proof uses classical weighted Cauchy-Schwarz, implemented "
                        + "by Holder with exponents 2 and 2, after splitting each "
                        + "product with sqrt((x/pi)^6-1). The dual-square densities "
                        + "are genuinely integrable. Scaling x=pi*s gives the "
                        + "Jacobian factors pi^(7/2) and pi. The normalized integrals "
                        + "of (s^(5/4)-1)^2/(s^6-1) and log(s)^2/(s^6-1) over s>1 "
                        + "are bounded by 3/40 and 3/160 respectively.")),
                Paragraph(Text(
                    "With s=exp(t), t>0, positive geometric layers and nonnegative "
                        + "Tonelli (MeasureTheory.lintegral_tsum) identify the dual "
                        + "integrals with their convergent coefficient series. "
                        + "Concrete integral-test tails supply the displayed rational "
                        + "bounds. Product integrability and the squared estimates "
                        + "then use MeasureTheory.integral_mul_norm_le_Lp_mul_Lq. "
                        + "These are applications of classical analysis and pinned "
                        + "Mathlib APIs; no unique literature originality is claimed.")),
                Paragraph(Text(
                    "The complete mirrored registration varies only D(U) in the "
                        + "first bound, retaining the second bound and both domains "
                        + "literally. Actual dependence compares U=0 with the H6 "
                        + "indicator U=1 on (2*pi,3*pi], whose excess integral is "
                        + "finite and positive. The rejected constant readout -1 "
                        + "contradicts the first bound at U=0. These moment "
                        + "estimates alone do not establish RH."))),
            DescribeRole.Theorem))));
}
