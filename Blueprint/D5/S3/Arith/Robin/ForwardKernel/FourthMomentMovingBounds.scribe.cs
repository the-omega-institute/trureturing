using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FourthMomentMovingBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthMomentMovingBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth moments of fixed increments control moving increments and integrable price-weighted profiles.",
        H("Moving fourth moments"),
        Blocks(
            Paragraph(Text(
                "Let E be a locally bounded measurable real function and "
                + "0<alpha<theta<beta<1. Suppose the integral of "
                + "abs(E(x+u)-E(x))^4 from 1 to Y is bounded by "
                + "C4*Y*u^2*log(Y/u)^2 throughout the exponent band "
                + "Y^alpha<=u<=Y^beta for all sufficiently large Y.")),
            Describe.Lean(
                DescribeId.Create("increment-pow-integrable-on"),
                DeclarationHandle.Create(Prefix + "increment_pow_integrableOn"),
                H("Powers of moving increments on compact sets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be locally bounded and Borel measurable, and let u and x be continuous real functions on a Hausdorff Borel space with a measure finite on compact sets. For every compact set K and natural number n, the function (E(x(p)+u(p))-E(x(p)))^n is integrable on K."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-increment-fourth-moment-bound"),
                DeclarationHandle.Create(Prefix + "moving_increment_fourth_moment_bound"),
                H("Uniform moving-increment fourth moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exists C>0 depending only on alpha, theta, and beta "
                        + "such that, for every E and C4 satisfying the hypotheses, for all sufficiently large X "
                        + "and every 0<=s<=1, the integral over [X,2X] of "
                        + "abs(E(x+s*x^theta)-E(x))^4 is at most "
                        + "C*C4*X*(X^theta)^2*log(X)^2. The threshold for X "
                        + "is independent of s.")),
                    Paragraph(Text(
                        "Set h=X^theta and L=s*x^theta. For v in [3h,4h], "
                        + "D_L(x)=D_v(x)-D_(v-L)(x+L), so its fourth power "
                        + "is at most eight times the sum of the two fourth "
                        + "powers. Average over v and enlarge the translated "
                        + "length interval to [h,4h]. Fubini reduces the "
                        + "transported term to fixed lengths w. The map "
                        + "x to x+s*x^theta has derivative at least one "
                        + "and image inside [1,3X], so the existing expanding "
                        + "change-of-variable estimate, applied to D_w squared, "
                        + "bounds each transported fourth moment by its "
                        + "fixed-length fourth moment. The exponent band "
                        + "contains all lengths in [h,4h] at Y=3X eventually. "
                        + "The resulting two averaged bounds are divided by h."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-response-fourth-moment-bound"),
                DeclarationHandle.Create(Prefix + "profile_response_fourth_moment_bound"),
                H("Fourth moments of integrable profiles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exists C>0 depending only on alpha, theta, and beta, "
                        + "such that for every E and C4 satisfying the hypotheses "
                        + "and every measurable real profile g integrable on [0,1], for all sufficiently "
                        + "large X, the integral of abs(profileResponse(x))^4/x "
                        + "over [X,2X] is at most C*C4*profileL1(g)^4 "
                        + "times (X^(1-theta)*log(X))^2.")),
                    Paragraph(Text(
                        "Write F(x) as the unit-interval integral of "
                        + "g(s)*D_(s*x^theta)(x)*rho_x(s*x^theta). Two "
                        + "applications of weighted Cauchy–Schwarz give "
                        + "abs(F(x))^4<=profileL1(g)^3 times the integral "
                        + "of abs(g(s))*abs(D_(s*x^theta)(x))^4, since the "
                        + "price ratio lies between zero and one. Local "
                        + "boundedness and profile integrability justify "
                        + "Fubini, after which the uniform moving-increment "
                        + "bound applies. The normalization identity gives "
                        + "abs(profileResponse(x))^4/x=x/(x^theta)^4*F(x)^4. "
                        + "On [X,2X] its scalar factor is at most "
                        + "2X/(X^theta)^4, yielding the asserted scale. "
                        + "The argument also includes profiles of zero L1 size."))),
                DescribeRole.Theorem))));
}
