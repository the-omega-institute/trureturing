using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MomentTransferWeightsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dyadic normalization separates the position factor from a price correction tending uniformly to one.",
        H("Normalization and price corrections"),
        Blocks(
            Paragraph(Text(
                "Let E be measurable and bounded on compact intervals, let g be a real integrable "
                + "profile on the unit interval, and write r=(1-theta)/2, U=x/X, "
                + "B(s,x)=D_(s*x^theta)(x)/sqrt(x^theta*log(x)).")),
            Describe.Lean(
                DescribeId.Create("logarithmic-factor-bounds"),
                DeclarationHandle.Create(Prefix + "logarithmic_factor_bounds"),
                H("Uniform logarithmic bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For X>=4 and X<=x<=2X, sqrt(log(x)/log(X)) is at least one and exceeds one by at most log(2)/log(X)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-z-eq-weighted-integral"),
                DeclarationHandle.Create(Prefix + "dyadicZ_eq_weighted_integral"),
                H("The normalized weighted integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For theta>0, X>=4, and X<=x<=2X, the normalized response Z equals "
                    + "U^r*sqrt(log(x)/log(X)) times the integral of g(s)*B(s,x)*rho_x(s*x^theta) "
                    + "over the unit interval. The unit-interval substitution is supplied by "
                    + "WeightRemoval.normalized_eq; the remaining factors follow from the "
                    + "positive square roots of the local and dyadic variance scales."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eventually-normalized-price-factor"),
                DeclarationHandle.Create(Prefix + "eventually_normalized_price_factor"),
                H("Uniform convergence of the price correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<theta<1 there is an eventually nonnegative function eta(X) tending "
                    + "to zero such that |sqrt(log(x)/log(X))*rho_x(s*x^theta)-1|<=eta(X) "
                    + "throughout X<=x<=2X and 0<=s<=1. One may take "
                    + "eta(X)=log(2)/log(X)+4*X^(theta-1). The logarithmic factor is at least "
                    + "one and differs from one by at most log(2)/log(X), while "
                    + "WeightControl.price_bounds and priceRatio_sub_one control the price ratio."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-b-uniform-bound"),
                DeclarationHandle.Create(Prefix + "dyadicB_uniform_bound"),
                H("Boundedness on a fixed rectangle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each real theta and each X>=4, there is a finite nonnegative bound "
                    + "for |B(s,x)| on 0<=s<=1 and X<=x<=2X. Compact boundedness of the "
                    + "increments and continuity of the reciprocal positive denominator give this bound. "
                    + "It supplies integrability on fixed rectangles, independently of the uniform "
                    + "moment estimate used in the limit."))),
                DescribeRole.Theorem))));
}
