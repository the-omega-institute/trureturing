using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class OwnClockFixedSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/OwnClockFixedSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact nonlinear own-clock gap on a fixed prime support.",
        H("Fixed support and own clock"),
        Blocks(
            Paragraph(Text("Let S be any finite set of natural primes with cardinal at least three. Real vectors satisfy x_p>=1 on S. Define theta=sum_S log p, L(x)=sum_S x_p log p, g(L)=log(log L), and Phi(x)=EulerGamma+g(L(x))-sum_S f_p(x_p), with the literal Euler factors of BoundaryPrimePrice. R_S is sInf of the image of this same Phi on this same domain; attainment and uniqueness are not asserted. The canonical reciprocal-log kernel gives lambda=1/(L log L), b_p=max(1,log(1+lambda^-1)/log p-1), T=L(b). T need not equal L.")),
            Describe.Lean(DescribeId.Create("own-clock-theta-domain"),
                DeclarationHandle.Create(Prefix + "theta_gt_one"), H("The fixed-support clock domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Prime bases are at least two. The canonical logarithm lower bound gives log 2>=1/2, so cardinal S>=3 implies theta>1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("own-clock-theta-lower"),
                DeclarationHandle.Create(Prefix + "theta_le_clock"), H("Every admissible clock lies above theta"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x_p>=1 on the fixed prime S, theta<=L(x), by positivity of each log p."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("own-clock-positive-domain"),
                DeclarationHandle.Create(Prefix + "clock_gt_one"), H("Every admissible clock exceeds one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combining the preceding inequalities pays the iterated-log domain condition for every admissible real vector."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("own-clock-price-positive"),
                DeclarationHandle.Create(Prefix + "own_price_pos"), H("The vector's own price is positive"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The price is ActualRobinClockCovariance.g evaluated at L(x), definitionally 1/(L(x)*log L(x)), and is strictly positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("own-clock-boundary-admissible"),
                DeclarationHandle.Create(Prefix + "own_boundary_admissible"), H("The price reference stays in the original real domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every b_p=max(1,c_p) is at least one on S. No unsupported prime is inserted, and its clock is the separate value T."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("own-clock-real-values-bounded"),
                DeclarationHandle.Create(Prefix + "real_values_nonempty_bdd_below"), H("A genuine real infimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constant vector one witnesses nonemptiness. The explicit lower bound EulerGamma+g(theta)+sum_S log(1-p^-1) follows from L>=theta, monotonicity of loglog, and log(1-p^(-x_p-1))<=0. Thus the image is bounded below without assuming the desired rounding theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("own-clock-real-infimum-bounds"),
                DeclarationHandle.Create(Prefix + "real_infimum_bounds"), H("Both conditional-infimum inequalities are paid"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("le_csInf gives the explicit baseline<=R_S; csInf_le gives R_S<=Phi(x) for every admissible x. Both use the actual nonempty bounded image, and the latter is applied to b."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("own-clock-tangent-remainder"),
                DeclarationHandle.Create(Prefix + "tangent_remainder_nonnegative"), H("Nonlinear terminal correction and its equality case"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For L,T>1, H=g(L)+(T-L)/(L log L)-g(T)>=0, and H>0 iff L!=T. The proof directly reuses RestrictedDivisorStrictInventory.loglog_tangent; the L=T case is retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("own-clock-exact-decomposition"),
                DeclarationHandle.Create(Prefix + "own_clock_decomposition"), H("The exact three-term own-clock identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every admissible real x, Phi(x)-R_S=(Phi(b)-R_S)+sum_S J_p(x_p)+[g(L)+lambda*(T-L)-g(T)]. All three terms are nonnegative: b belongs to the infimum domain, BoundaryPrimePrice supplies each real price comparison, and the existing nonlinear tangent gives the last sign. The sum identity retains lambda at x's L while Phi(b) uses T."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("own-clock-all-integer-gap"),
                DeclarationHandle.Create(Prefix + "all_integer_gap"), H("Every integer vector pays the full finite rounding sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every a:S->Z with a_p>=1, 0<=sum_S d_p(lambda_L)<=Phi(a)-R_S. The scalar attained candidate compares each arbitrary a_p with the actual integer price maximum. No optimality of a, equality T=L, initial support, attained real minimizer or desired lower-bound hypothesis is used. This supplements the existing qualitative allocation theorem uniform_min_tail_robin_lower; it does not duplicate that theorem, fixed-budget KL, or the failure-side optimizer reduction. The explicit six-band prime-count stage remains separate and unpaid."))), DescribeRole.Theorem))));
}
