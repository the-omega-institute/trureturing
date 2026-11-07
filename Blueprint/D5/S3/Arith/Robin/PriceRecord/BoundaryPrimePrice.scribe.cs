using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class BoundaryPrimePriceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uncompiled source candidate: boundary-one prime price loss and exact integer rounding.",
        H("Boundary-one price loss: uncompiled candidate"),
        Blocks(
            Paragraph(Text("All scalar parameters are real. Assume p>1, lambda>0 and t>=1. Set f_p(t)=log((1-p^(-t-1))/(1-p^-1)), F_p(t)=f_p(t)-lambda*t*log p, C=1+lambda^-1, c=log C/log p-1 and b=max(1,c). The domain is fixed at exponent at least one. Bernoulli KL is the existing D5/S0/Diagonal/MarginBound.bernoulliKL, with its existing nonnegativity theorem; it is not redefined here. Every statement in this document is a source candidate awaiting canonical kernel and Scribe checks.")),
            Describe.Lean(DescribeId.Create("boundary-price-probability-domain"),
                DeclarationHandle.Create(Prefix + "probability_mem"), H("Euler probabilities lie in the open unit interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For p>1 and t>=1, 0<p^(-t-1)<1. This pays the logarithm and KL domain conditions in the subsequent proofs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-price-benefit-log"),
                DeclarationHandle.Create(Prefix + "benefit_log"), H("Separate the two Euler logarithms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under those same conditions, f_p(t)=log(1-p^(-t-1))-log(1-p^-1), with both positive logarithm arguments established."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-price-maximum"),
                DeclarationHandle.Create(Prefix + "boundary_maximum"), H("The real maximum on the boundary-one domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real t>=1, F_p(t)<=F_p(b). The proof consumes ContinuousPrimeMaximum.continuous_prime_hasDerivAt and continuous_prime_slope_strictAntiOn, establishes the shifted critical point and its boundary slope, and derives increase before b and decrease after b. The existing exponent-zero maximum is not substituted for this domain."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-price-integer-candidates"),
                DeclarationHandle.Create(Prefix + "integer_candidates"), H("Two candidates dominate every integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every integer k>=1 satisfies F_p(k)<=max(F_p(floor b),F_p(ceil b)). Both candidates are admissible. Monotonicity on either side of b proves the exhaustive comparison, including integral b and ties."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-price-integer-gap-bounds"),
                DeclarationHandle.Create(Prefix + "integer_gap_bounds"), H("A nonnegative loss for every integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write J_p(t)=F_p(b)-F_p(t) and d_p=min(J_p(floor b),J_p(ceil b)). For every integer k>=1, 0<=d_p<=J_p(k). No optimality of k is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-price-integer-gap-attained"),
                DeclarationHandle.Create(Prefix + "integer_gap_attained"), H("The finite loss is the exact integer price gap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One admissible integer k attains d_p=J_p(k) and dominates F_p(j) for every integer j>=1. Choosing either smaller candidate loss remains valid at a tie. This result is consumed by the full-vector lower bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-price-general-kl-difference"),
                DeclarationHandle.Create(Prefix + "price_difference_kl"), H("KL difference with the real reference retained"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all real x,t>=1 and every real lambda, put v=p^(-x-1), u=p^(-t-1). Then F_p(x)-F_p(t)=D_Ber(v||u)/(1-v)+(lambda-1/(p^(x+1)-1))*(t-x)*log p. The log-ratio and odds identities are proved, so the linear boundary term is not dropped."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-price-active-loss"),
                DeclarationHandle.Create(Prefix + "active_loss"), H("The active KL and logarithmic formulas"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If p^2<C, then c>1 and for every real t>=1, J_p(t)=D_Ber(C^-1||p^(-t-1))/(1-C^-1)=log((1-C^-1)/(1-p^(-t-1)))-lambda*log(C/p^(t+1)). The Bernoulli orientation and denominator are literal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-price-inactive-loss"),
                DeclarationHandle.Create(Prefix + "inactive_loss"), H("The inactive boundary KL and excess price"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If C<=p^2, then b=1, d_p=0, lambda-1/(p^2-1)>=0 and J_p(t)=D_Ber(p^-2||p^(-t-1))/(1-p^-2)+(lambda-1/(p^2-1))*(t-1)*log p for every t>=1. The scaled KL is nonnegative by the canonical Bernoulli theorem. Equality C=p^2 is included and then the excess-price coefficient vanishes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundary-price-active-integer-gap"),
                DeclarationHandle.Create(Prefix + "active_integer_gap"), H("The explicit active two-KL minimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For p^2<C, d_p is exactly the minimum of D_Ber(C^-1||p^(-k-1))/(1-C^-1) at k=floor c and k=ceil c. The scalar formulas and two-candidate comparison are inputs to OwnClockRobinGap.original_margin_own_clock_gap. The derivation is repository mathematics informed by the supplied terminal paper and independent mathematical review; neither paper evidence nor this uncompiled source is Lean acceptance. No classical constant, six-band estimate or RH assertion is claimed here."))), DescribeRole.Theorem))));
}
