using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class MellinWeightedVariationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/MellinWeightedVariation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An absolute Mellin moment bounds the full weighted variation of the Robin integral kernel.",
        H("Mellin Weighted Variation"),
        Blocks(
            Paragraph(Text(
                "For t>1, let w(t)=(log(t)+1)/(t^2*log(t)^2). For positive scale s "
                + "and positive y, set f(s,y)=s*w(s*y). The clipped kernel q(x,s,y) "
                + "equals f(s,y) when x/s<y and zero otherwise. At the threshold "
                + "x/s=y the kernel is zero. Real powers denote Real.rpow.")),
            Paragraph(Text(
                "Write L=log(x), h1=1+1/L and h2=1+2/L+2/L^2. The coefficient "
                + "C(x,alpha)=x^(alpha-1)/L*(h1+h2/(1-alpha)) is positive "
                + "for x>1 and 0<alpha<1.")),
            Describe.Lean(
                DescribeId.Create("clipped-kernel-prefix"),
                DeclarationHandle.Create(Prefix + "clipped_kernel_prefix_bound"),
                H("Every pointwise prefix has one common bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural N, every x>1, every y>0 and every "
                        + "0<alpha<1, the sum over 0<=j<N of "
                        + "(j+1)^alpha*|q(x,j+1,y)-q(x,j+2,y)| is at most "
                        + "C(x,alpha)*y^(-alpha-1). The bound is independent of N.")),
                    Paragraph(Text(
                        "Put a=x/y. The indicator chi(a,s), equal to one for s<=a "
                        + "and zero otherwise, pays for the single threshold crossing. "
                        + "The decreasing potential max(s,a)^(alpha-1) pays for "
                        + "the smooth kernel decrease. Both differences telescope "
                        + "over adjacent natural scales, retaining the strict cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-prefix"),
                DeclarationHandle.Create(Prefix + "generic_weighted_prefix"),
                H("The pointwise estimate transports to integral prefixes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a measurable real function. Assume that "
                        + "|rho(y)|*y^(-alpha-1) is Lebesgue integrable on y>0, "
                        + "and write M(rho,alpha) for its integral. Define "
                        + "P(rho,x,s) as the integral on y>0 of rho(y)*q(x,s,y). "
                        + "For every natural N, x>1 and 0<alpha<1, the sum over "
                        + "0<=j<N of (j+1)^alpha*|P(rho,x,j+1)-P(rho,x,j+2)| "
                        + "is at most C(x,alpha)*M(rho,alpha).")),
                    Paragraph(Text(
                        "The Mellin majorant proves absolute integrability of "
                        + "each clipped integral before integral subtraction. "
                        + "The triangle inequality and the finite pointwise sum "
                        + "then give the prefix bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-weighted-variation"),
                DeclarationHandle.Create(Prefix + "mellin_weighted_variation"),
                H("Summability and the complete infinite sum bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every measurable real rho, every x>1 and every "
                        + "0<alpha<1 with the stated absolute Mellin integrability, "
                        + "the sequence (j+1)^alpha*|P(rho,x,j+1)-P(rho,x,j+2)| "
                        + "is summable over all natural j. Its infinite sum is at "
                        + "most C(x,alpha)*M(rho,alpha). Both conclusions follow "
                        + "from the nonnegative prefix sums with the common bound.")),
                    Paragraph(Text(
                        "The whole positive y axis is retained, including y<1. "
                        + "Measurability and absolute Mellin integrability are "
                        + "the function hypotheses; continuity and a derivative "
                        + "of rho are not required. Applying this analytic bound "
                        + "to an arithmetic residual still requires its actual "
                        + "Mellin integrability. The estimate supplies no bound "
                        + "on the independent signed arithmetic coefficient sums."))),
                DescribeRole.Theorem))));
}
