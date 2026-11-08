using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class DyadicMeanSquareAsymptoticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The variance band gives the profile-kernel mean-square law and strict excursions on sets of positive measure.",
        H("Dyadic profile-kernel asymptotics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dyadic-point-weight-integral-tendsto"),
                DeclarationHandle.Create(Prefix + "dyadic_point_weight_integral_tendsto"),
                H("The dyadic point weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<theta<1, the integral of x^(1-theta) log(x)/x on [X,2X], divided by X^(1-theta) log X, tends to (2^(1-theta)-1)/(1-theta). Substitution x=Xv leaves the integral of v^(-theta) on [1,2], plus a fixed logarithmic integral divided by log X."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-kernel-dyadic-mean-square-asymptotic"),
                DeclarationHandle.Create(Prefix + "profile_kernel_dyadic_mean_square_asymptotic"),
                H("The profile-kernel mean-square law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be measurable and bounded on compact intervals, 0<alpha<theta<beta<1, and assume the uniform cumulative variance asymptotic on that exponent band. For every real integrable Borel profile g, the integral of the square of its price-kernel response with measure dx/x on [X,2X], divided by X^(1-theta) log X, tends to Q(g)(2^(1-theta)-1). Price removal is negligible in the normalized L2 norm. The reverse triangle inequality transfers the moving-profile limit to the price-kernel response. No von Koch bound or separate short-interval upper hypothesis is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-kernel-dyadic-large-set"),
                DeclarationHandle.Create(Prefix + "profile_kernel_dyadic_large_set"),
                H("Strict excursions on a set of positive measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same hypotheses, if g is not zero almost everywhere and 0<c<sqrt((1-theta)Q(g)), every sufficiently large [X,2X] has a positive-measure set where the absolute response is strictly greater than c x^((1-theta)/2) sqrt(log x). Positivity of Q(g) follows from its tail-energy representation. A zero-measure excursion set would bound the square integral almost everywhere by c squared times the dyadic point weight, contradicting the strict gap between their limiting constants."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For Corollary 490.7, take E=psi-id, theta=4/5, g=1, alpha=3/4, beta=7/8. The identity forwardResponse_eq_profileResponse identifies the kernel. The integral_min_unit_square formula gives Q(1)=1/3, so the mean-square limit is (2^(1/5)-1)/3 and the excursion threshold is sqrt((1/5)(1/3))=1/sqrt(15). The positive-measure strict conclusion implies the earlier non-strict point conclusion. These substitutions use only the band asymptotic and the established local bounded measurability of psi-id.")))));
}
