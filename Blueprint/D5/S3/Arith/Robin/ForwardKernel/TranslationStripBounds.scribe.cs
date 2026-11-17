using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class TranslationStripBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/TranslationStripBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Comparable cumulative variances control translations and short strips of moving increments.",
        H("Translation and short-strip bounds"),
        Blocks(
            Paragraph(Text(
                "Let E be a locally bounded measurable real function and write "
                + "z_t(x)=E(x+t*x^b)-E(x), where 0<b<1 and 0<=t<=1. "
                + "A comparison scale R is eventually positive, and its cumulative "
                + "variances at all lengths in each fixed interval [c1*R,c2*R] "
                + "and each fixed spatial enlargement d*X are bounded by "
                + "a constant times X*R*log(X). All interval estimates below "
                + "hold on any fixed [A*X,B*X] with 0<A<=B.")),
            Describe.Lean(
                DescribeId.Create("comparable-length-variance-upper-of-band"),
                DeclarationHandle.Create(Prefix + "comparableLengthVarianceUpper_of_band"),
                H("Interior power scales"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If 0<alpha<rho<beta<1 and E satisfies the uniform "
                    + "cumulative-variance band asymptotic between alpha and beta, "
                    + "then R(X)=X^rho satisfies the comparable-length upper bound. "
                    + "This applies MovingLengthVariance.comparable_length_variance_bound "
                    + "directly; positivity of the power supplies positivity of the scale."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-sq-integrable"),
                DeclarationHandle.Create(Prefix + "moving_sq_integrable"),
                H("Integrability of moving-increment squares"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a locally bounded measurable E and a positive exponent b, "
                    + "the square of E(x+t*x^b)-E(x) is integrable on every finite "
                    + "interval, for every real t. The endpoint maps are continuous, "
                    + "so their images on a compact interval are compact."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-increment-translation-square-bound"),
                DeclarationHandle.Create(Prefix + "moving_increment_translation_square_bound"),
                H("Square integral of a translation difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose R satisfies the comparable-length upper bound and "
                        + "R(X)=O(X^b). There is a positive constant C and one eventual "
                        + "threshold such that, simultaneously for every t in [0,1], "
                        + "every v in [0,R(X)], and every interval [l,r] inside "
                        + "[A*X,B*X], the integral of "
                        + "(z_t(x+v)-z_t(x))^2 is at most C*X*R(X)*log(X).")),
                    Paragraph(Text(
                        "For psi(x)=x+t*x^b, decompose the translation difference "
                        + "as E(psi(x+v))-E(psi(x)) minus E(x+v)-E(x). "
                        + "The derivative of psi lies between one and two for x>=1, "
                        + "so its translated endpoints have gap between zero and 2*v. "
                        + "Apply MovingEndpointVariance.two_endpoint_increment_square_le "
                        + "to each pair of endpoints, then use the square inequality "
                        + "for their difference. The eventual bound R(X)<=X places "
                        + "all endpoints inside [1,(2*B+2)*X]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-increment-translation-l2-bound"),
                DeclarationHandle.Create(Prefix + "moving_increment_translation_l2_bound"),
                H("Square-root norm of a translation difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same assumptions, the interval square-root norm "
                    + "of z_t(x+v)-z_t(x) is at most "
                    + "C*sqrt(X*log(X))*sqrt(R(X)). The constant and eventual "
                    + "threshold are simultaneous in t, v, l and r. "
                    + "Take square roots of the translation square estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-square-bound-of-comparable"),
                DeclarationHandle.Create(Prefix + "moving_square_bound_of_comparable"),
                H("Square mass of a moving increment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be locally bounded and measurable and 0<b<1. "
                    + "If X^b satisfies the comparable-length cumulative-variance "
                    + "upper bound, then for every fixed 0<A<=B there is C>0 "
                    + "such that, eventually in X, simultaneously for t in [0,1], "
                    + "the integral of (E(x+t*x^b)-E(x))^2 over [A*X,B*X] "
                    + "is at most C*X*X^b*log(X). Apply the two-endpoint "
                    + "increment estimate with endpoints x and x+t*x^b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-increment-short-strip-square-bound"),
                DeclarationHandle.Create(Prefix + "moving_increment_short_strip_square_bound"),
                H("Square mass on a short strip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose T and X^b satisfy the comparable-length upper "
                        + "bounds and T(X)=O(X^b). There is a positive constant C "
                        + "and one eventual threshold such that, simultaneously "
                        + "for t in [0,1], every M>=0 and every interval [l,r] "
                        + "inside [A*X,B*X] with r-l<=M, the integral of z_t(x)^2 "
                        + "is at most C*X*log(X)*(M*X^b/T(X)+T(X)). "
                        + "No positive lower bound on the interval length is required.")),
                    Paragraph(Text(
                        "Average z_t(x)^2<=2*z_t(x+v)^2 "
                        + "+2*(z_t(x+v)-z_t(x))^2 over 0<=v<=T(X). "
                        + "After Fubini, the shifted term is bounded by the strip "
                        + "length times the total square mass on [A*X,(B+1)*X]. "
                        + "The two-endpoint increment estimate bounds that mass "
                        + "by O(X*X^b*log(X)). The translation square estimate "
                        + "bounds the other term. Local boundedness and "
                        + "measurability justify all rectangle integrals."))),
                DescribeRole.Theorem))));
}
