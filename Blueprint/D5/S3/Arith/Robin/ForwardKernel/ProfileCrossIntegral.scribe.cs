using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class ProfileCrossIntegralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform bounds for moving-increment primitives control cross integrals of weighted profiles.",
        H("From covariance to profile cross integrals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("profile-cross-integral-of-covariance-bound"),
                DeclarationHandle.Create(Prefix + "profile_cross_integral_of_covariance_bound"),
                H("Uniform profile estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be measurable and bounded on every compact interval, let "
                        + "0<a,b<1, and let B be any nonnegative function. Suppose a constant C0 "
                        + "bounds the absolute integral from X to y of "
                        + "(E(x+s*x^a)-E(x))*(E(x+t*x^b)-E(x)) by C0*B(X), "
                        + "uniformly for s,t in [0,1] and y in [X,2X], for all sufficiently large X. "
                        + "Then a positive constant C bounds the absolute integral over [X,2X] "
                        + "of profileResponse(E,a,g1,x)*profileResponse(E,b,g2,x)/x by "
                        + "C*profileL1(g1)*profileL1(g2)*X^(-a-b)*B(X). "
                        + "Both C and the threshold are independent of the integrable profiles.")),
                    Paragraph(Text(
                        "The exact normalized response formula expresses the cross integral "
                        + "as an integral over the two profile parameters of weighted covariance. "
                        + "On each fixed compact spatial interval, local boundedness of E "
                        + "dominates the joint integrand by a constant times |g1(s)*g2(t)|, "
                        + "which justifies Fubini. The weight is "
                        + "W(x)=x^(-a-b)*priceRatio(x,s*x^a)*priceRatio(x,t*x^b). "
                        + "The price-ratio derivative bound gives "
                        + "|W(2X)|+integral_X^(2X)|W'(x)| dx <= (27+a+b)*X^(-a-b). "
                        + "Integration by parts for the absolutely continuous covariance primitive "
                        + "then gives the stated estimate after integration against |g1(s)*g2(t)|."))),
                DescribeRole.Theorem))));
}
