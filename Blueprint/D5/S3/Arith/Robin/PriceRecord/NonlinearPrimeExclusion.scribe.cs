using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class NonlinearPrimeExclusionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/NonlinearPrimeExclusion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same original Robin minimum has nonlinear deletion and insertion roots with an open prime-free interval.",
        H("Nonlinear prime exclusion at the original minimum"),
        Blocks(
            Paragraph(Text("For real x>1 set A_L(x)=L-L^(x/(x+1))-log x and B_L(x)=log x-L^(1+1/x)+L. These are deletionBarrier and insertionBarrier; NonlinearPrimeGap records their roots, uniqueness on all x>1, the strict ordering and the all-prime weak endpoint implication.")),
            Describe.Lean(
                DescribeId.Create("same-original-minimum-nonlinear-prime-gap"),
                DeclarationHandle.Create(Prefix + "failure_has_nonlinear_prime_gap"),
                H("The original nonpositive failure constructs the same minimum and both barriers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The sole premise is an integer n>5040 with robinLogMargin(n)<=0, including equality. The conclusion preserves every component of failure_has_unique_half_shift_cutoff for the SAME N and z: N>55440, nonpositive original margin, attained global minimum over every m>5040, positive own price below boundaryPrice, fixed-price golden optimality and strict advantage over each distinct positive integer, both strictInteger and maximalInteger identities, all-prime/layer absence of activation ties, z>11, 0<log N-z<1/2, the real first-layer price equation, uniqueness of that cutoff on all t>1, and exact inclusive floorNat(z) prime support. It adds real alpha,beta with L/2<alpha<z<L<beta, A_L(alpha)=B_L(beta)=0, uniqueness of each root on all x>1, and for every prime p, alpha<p implies beta<=p, where L=log N.")),
                    Paragraph(Text("The public finite Robin bound forces this nonpositive N>=223092870. Since exp(1)<3 and 3^16=43046721<223092870, L>16. Boundary divisibility follows from weak_dvd_weak at the own price and boundaryPrice, with boundaryCap_eq_55440. For every prime divisor p, the actual integer cofactor N/p exceeds 5040: for p<=11 use 5040p<=55440<N; for p>11 use primality, coprimality with 55440 and exact divisibility cancellation. Integer division is used only with p dividing N.")),
                    Paragraph(Text("Order monotonicity of real powers and logarithms proves A_L strictly antitone and B_L strictly monotone on x>1. The bound log L<=3+L/16 gives 2+2log L<L. The strict exponential inequality yields A_L(L/2)>0. Strict loglog_tangent at L and L-log z, with its positive domain proved, gives A_L(z)<0. Also B_L(L)<0 and B_L(exp(L^2))>0. Continuity and finite IVT intervals construct the roots; full-domain monotonicity proves their uniqueness.")),
                    Paragraph(Text("For a support prime p>alpha, the existing endpoint_first_layer_band gives v_p(N)=1 from largestPrime(N)<=z<L and L>16. The existing golden_resource_objective_single_layer_delta at price zero, golden_resource_sigma_identity and first-layer marginal formula give the exact W increment at N/p. The original minimum comparison with that legal cofactor forces A_L(p)>=0, contradicting antitonicity past alpha. For a fresh prime, the same delta at N and the original minimum comparison with Np force B_L(p)>=0, hence p>=beta. Thus the excluded interval is OPEN(alpha,beta); alpha may be a support prime and beta may be a missing prime. No uniqueness of the original margin minimizer is asserted.")),
                    Paragraph(Text("The half-log scale overlaps published work of Caveney--Nicolas--Sondow and Wu, Properties of counterexample to Robin hypothesis, arXiv:1901.09832v2. Wu's Theorems 6 and 7 use different strict or very large-domain hypotheses; they are not Lean suppliers here, and no novelty claim is made. This result controls first-layer prime locations using actual nonlinear comparisons. It asserts no signed far-tail lower bound, full integral sign, Robin conclusion or RH. Escape registration is a source-bound attempt whose machine validation is reported separately."))),
                DescribeRole.Theorem))));
}
