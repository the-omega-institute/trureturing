using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class WeightRemovalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/WeightRemoval.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Price removal for integrable moving profiles has a negligible mean-square error.",
        H("Removing the price weight from profiles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-profile-integral-bound"),
                DeclarationHandle.Create(Prefix + "weighted_profile_integral_bound"),
                H("Uniform bound for the price-weighted profile integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an integrable profile g, x>=3, and a nonnegative uniform bound M for abs(E(x+s*x^theta)-E(x)) on 0<=s<=1, the absolute unit integral of g(s) times this increment times priceRatio(x,s*x^theta) is at most profileL1(g)*M. The price ratio lies between zero and one."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Let E be locally bounded and Borel measurable, let g be an integrable "
                + "Borel profile on (0,1), and put H(x)=x^theta. The unweighted response "
                + "is sqrt(x)*P(H(x),g,x), where P is the profile average. The weighted "
                + "response inserts rho(x,u)=w(x+u)/w(x) into the defining integral.")),
            Describe.Lean(
                DescribeId.Create("price-measurable"),
                DeclarationHandle.Create(Prefix + "price_measurable"),
                H("Joint measurability of the price ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The map (x,u) to w(x+u)/w(x) is Borel measurable, "
                    + "using the explicit logarithmic formula for w."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-eq"),
                DeclarationHandle.Create(Prefix + "normalized_eq"),
                H("Exact unit-profile representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For x>0 and any real exponent theta, the weighted profile "
                    + "response divided by sqrt(x) equals x^(-theta) times "
                    + "the integral over s in (0,1) of g(s), the increment "
                    + "E(x+s*x^theta)-E(x), and the price ratio at that displacement. "
                    + "This is the change of variables u=s*x^theta in the "
                    + "defining profile integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-increment-bound"),
                DeclarationHandle.Create(Prefix + "local_increment_bound"),
                H("Uniform compact bound for moving increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For locally bounded measurable E, any real theta and "
                    + "0<a<=b, there is M>=0 bounding the absolute value of "
                    + "E(x+s*x^theta)-E(x) simultaneously for a<=x<=b and "
                    + "0<=s<=1. Continuity bounds x^theta on the compact "
                    + "spatial interval, and local boundedness controls both endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("increment-measurable"),
                DeclarationHandle.Create(Prefix + "increment_measurable"),
                H("Joint measurability of moving increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For locally bounded Borel measurable E and every real "
                    + "theta, the map (x,s) to E(x+s*x^theta)-E(x) is Borel "
                    + "measurable. This follows by composing E with the "
                    + "measurable endpoint maps and subtracting."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-response-normalized-mem-lp"),
                DeclarationHandle.Create(Prefix + "profileResponse_normalized_memLp"),
                H("Local square integrability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real theta and every 3<=a<=b, the weighted response "
                    + "divided by sqrt(x) belongs to L2([a,b],dx). Rescaling to (0,1) "
                    + "shows measurability. Compact boundedness of the increments, "
                    + "0<=rho<=1, and positivity of x^theta give a uniform bound "
                    + "by a constant times the L1 norm of g."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-response-aestrongly-measurable"),
                DeclarationHandle.Create(Prefix + "profileResponse_aestronglyMeasurable"),
                H("Measurability of the weighted response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For locally bounded Borel measurable E, an integrable Borel profile g, "
                    + "any real theta and 3<=a<=b, the weighted profile response is almost "
                    + "everywhere strongly measurable on (a,b] with respect to Lebesgue measure. "
                    + "Multiply the already square-integrable response divided by sqrt(x) "
                    + "by the continuous function sqrt(x)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-weight-removal-pointwise"),
                DeclarationHandle.Create(Prefix + "profile_weight_removal_pointwise"),
                H("Pointwise arithmetic error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<theta<1, assume the von Koch bound "
                    + "|E(x)|<=C*sqrt(x)*log(x)^2 eventually. The difference between "
                    + "weighted and unweighted responses is "
                    + "O(log(x)^2 times the integral of s*|g(s)| on (0,1)). "
                    + "The displacement bound 1-rho(x,u)<=4*u/x and the uniform "
                    + "von Koch bound for increments of length at most x^theta "
                    + "give this estimate for arbitrary integrable profiles."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-weight-removal-l2"),
                DeclarationHandle.Create(Prefix + "profile_weight_removal_l2"),
                H("Negligible mean-square error from the variance band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume a variance asymptotic uniform on the exponent band "
                    + "0<alpha<theta<beta<1. The integral of the squared difference "
                    + "between weighted and unweighted responses against dx/x on "
                    + "[X,2X], divided by X^(1-theta)*log(X), tends to zero. "
                    + "No von Koch hypothesis is needed. The normalized error is "
                    + "bounded by 4/x times the integral of s*|g(s)|*|D(s*x^theta,x)|. "
                    + "Weighted Cauchy-Schwarz, Fubini, and the uniform moving-increment "
                    + "variance estimate bound its squared L2 norm by "
                    + "16*C*norm(s*g,1)^2*X^(-2)*X*X^theta*log(X). "
                    + "The ratio to the mean-square scale is at most "
                    + "16*C*norm(s*g,1)^2*X^(2*theta-2), which tends to zero."))),
                DescribeRole.Theorem))));
}
