using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualFactorialCumulativePositivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual signed factorial error has positive cumulative mass and gives a positive representation and strict budgets for the complete Robin high remainder.",
        H("Signed Factorial Cumulative Positivity and the Complete High Integral"),
        Blocks(
            Paragraph(Text(
                "Use the existing actual error eta(y)=log(floor(y)!)-y*log(y)+y. "
                + "Its pointwise sign is unrestricted. Define C(Y) as the interval integral "
                + "from 1 to Y of eta(y)/y^2, and kappa=log(2)*(1-log(2))/2. "
                + "The remainder h(r) is exactly the existing highRemainder(r), "
                + "with every factorial source and the entire original high kernel retained.")),
            Describe.Lean(
                DescribeId.Create("actual-factorial-cumulative-positivity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualFactorialCumulativePositivity.result"),
                H("Positive cumulative mass and its complete high-integral consumer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every Y>=1, log(Y)/Y<=C(Y)<=2-(log(Y)+2)/Y<2. "
                        + "The exact endpoints are C(1)=0 and C(2)=log(2)-log(2)^2/2. "
                        + "For Y>1 the cumulative mass is strictly positive. "
                        + "For Y>=2 the lower bound improves to kappa+log(Y)/Y<=C(Y), "
                        + "where kappa is strictly positive.")),
                    Paragraph(Text(
                        "The original scalar sum_log_floor_lower gives eta(y)>=1-log(y) "
                        + "on y>=1. Its lower primitive is log(y)/y; the absolute error "
                        + "envelope gives the upper primitive -(log(y)+2)/y. "
                        + "On the open interval (1,2), floor(y)=1 and eta(y)/y^2="
                        + "(1-log(y))/y. Its exact integral supplies the retained kappa "
                        + "when the lower comparison is continued from 2. "
                        + "The singleton at 2 is removed using the library's null-endpoint identity.")),
                    Paragraph(Text(
                        "For r>0 set J(r,y)=((r+log(y))^(-2)+2*(r+log(y))^(-3))/y. "
                        + "The complete positive representation is "
                        + "h(r)=integral over u>0 of C(exp(u))*"
                        + "((r+u)^(-2)+2*(r+u)^(-3)). "
                        + "Its equivalent y representation is the integral over y>1 "
                        + "of C(y)*J(r,y); that integrand is integrable on the entire domain.")),
                    Paragraph(Text(
                        "Absolute Fubini is paid before the swap. The density eta(y)/y^2 "
                        + "is absolutely integrable by the original factorial envelope. "
                        + "J is positive and integrable, with tail integral "
                        + "(r+log(a))^(-1)+(r+log(a))^(-2) at every a>=1. "
                        + "The triangular product 1_(y<z)*(eta(y)/y^2)*J(r,z) "
                        + "is therefore integrable under the product of the two restricted measures. "
                        + "Integrating z first recovers the literal signed high kernel; "
                        + "integrating y first gives C(z). The exponential change of variables "
                        + "then gives the displayed u representation. Neither eta nor its floor "
                        + "factorial is differentiated.")),
                    Paragraph(Text(
                        "The actual complete signed h satisfies the strict budgets "
                        + "kappa*((r+log(2))^(-1)+(r+log(2))^(-2))<h(r)"
                        + "<2*(r^(-1)+r^(-2)). The lower comparison retains the "
                        + "kappa tail on y>2 and a strictly positive mass on (1,2). "
                        + "The upper comparison integrates the strictly positive deficit "
                        + "(2-C(y))*J(r,y). Both strict inequalities use positive-measure support, "
                        + "rather than a pointwise sign assertion about eta.")),
                    Paragraph(Text(
                        "The original LogConvolutionMassExpansion owns the scalar lower bound, "
                        + "factorial identity and error envelope. Those scalar proofs retain "
                        + "Terence Tao's Apache 2.0 attribution and immutable Mathlib source "
                        + "0826a5e4ff8877949060d03ce8955545bfb2b47f. "
                        + "ActualFactorialRobinHighDerivative.result supplies the literal eta "
                        + "identification and its highKernel_formula is consumed at its owner. "
                        + "QuotientIntegralBudget supplies residual measurability and the "
                        + "complete logarithmic envelope integrability. The present estimates "
                        + "are a repository derivation; no literature priority is asserted.")),
                    Paragraph(Text(
                        "The next same-object obligation is the dyadic signed weight "
                        + "q(r)=h(r)-h(r+log(2))/2 and its negative derivative. "
                        + "The exact low-part sign, anchored odd harmonic Mobius prefix estimate, "
                        + "infinite Robin pairing, Robin inequality and RH remain unproved here."))),
                DescribeRole.Theorem))));
}
