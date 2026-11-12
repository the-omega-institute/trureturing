using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualRecordHigherLayerResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete finite actual prime-layer loss and second-layer tube bounds.",
        H("Complete finite loss estimates"),
        Blocks(
            Paragraph(Text("Exact finite objects and completeness")),
            Paragraph(Text(
                "Use the library's actualPressure=sup of goldenResourceObjective(referencePrice(X),n) "
                + "over all n>=1, and its actualDefect=that pressure minus the objective of the same original "
                + "integer. The local pressureOptimizer notation reuses the canonical "
                + "ActualTwoPriceDefect.strictInteger(referencePrice(X)); its counts and optimality come "
                + "from strictInteger_counts and ActualGlobalBracketing.strict_is_optimal. lossPrimes is the union of that optimizer's primeFactors and "
                + "the original integer's primeFactors; no primes of zero original valuation are discarded. "
                + "For p,j put g=log(p)*(goldenLayerMarginal(p,j)-referencePrice(X)) and "
                + "ell=max(g,0)-1_{j<=v_p(n)}g. This equals max(-g,0) on occupied layers and max(g,0) "
                + "on missing layers, so every term is nonnegative.")),
            Paragraph(Text(
                "At each prime let c=optimalLayerCount(referencePrice(X),p), a=v_p(n), M=max(c,a). "
                + "positive_layers_eq_count_interval gives g>0 exactly for 1<=j<=c. Every j>M has zero "
                + "loss. Every prime outside lossPrimes has both optimizer and original valuation zero, "
                + "hence c=a=0 and every positive-index loss is zero. This proves that the finite functionals "
                + "are complete. C1 sums ell(p,1), C2 sums ell(p,2), and D3 sums ell(p,j) for 3<=j<=M, "
                + "over lossPrimes. Thus C1 includes ALL absent positive-gain first-layer primes and ALL "
                + "occupied negative-gain first-layer primes, with equality-price coordinates contributing zero.")),
            Paragraph(Text(
                "The private live lemma actual_defect_decomposition proves actualDefect=C1+C2+D3. "
                + "It evaluates the literal pressure at pressureOptimizer using the existing supremum and "
                + "optimal-count APIs, extends both objectives to their common finite prime support with "
                + "golden_resource_objective_sum_on, and uses local_eq_layer_sum. At each prime, "
                + "sum_{j<=M}max(g,0)=localObjective(c) while sum_{j<=M, j<=a}g=localObjective(a). "
                + "The interval split isolates 1,2,3..M, including M=0 and M=1. This lemma is consumed "
                + "in finite_actual_second_layer_tube_bound; it is not a replacement pressure definition.")),
            Describe.Lean(
                DescribeId.Create("actual-complete-higher-layer-finite-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherLayerResidual.finite_complete_higher_layer_bound"),
                H("The entire missing Euler tail is charged once per prime"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For X>1, every actual full predecessor record m>=2 at arbitrary mu>0, and any "
                        + "deterministic real R>=1 with R<P=largestPrime(m) and X log(X)<=log(2) R^3, "
                        + "the theorem gives 0<=D3, D3<=2 floor(R)/P+referencePrice(X)*M3(m), "
                        + "and D3<=2R/P+referencePrice(X)*Q3*log(4P^2). Here M3 is exactly the existing "
                        + "strict_inventory_third_layer_mass, with full original multiplicities.")),
                    Paragraph(Text(
                        "If a j>=3 raw margin is positive, the existing reciprocal-power marginal bound "
                        + "and log(p)>=log(2) give log(2)*p^3<X log(X)<=log(2)*R^3, hence p<R. "
                        + "This is a derived profitable-coordinate cutoff, not an imposed support bound. "
                        + "It eliminates every missing higher contribution at p>=R, including p=P and p>P. "
                        + "For each smaller prime p, retain the actual valuation a=v_p(m), including a=0. "
                        + "The sum of its missing profitable higher gains is no larger than the finite raw "
                        + "tail from a+1 to c. The existing local_eq_layer_sum at price zero telescopes "
                        + "that sum to localObjective(0,c)-localObjective(0,a), which is at most "
                        + "-log(1-p^{-(a+1)}). No infinite sum is used.")),
                    Paragraph(Text(
                        "Apply ExponentExchange.PriceRecordMissingLayer.price_record_missing_layer "
                        + "DIRECTLY with this original m, original mu, largest prime P dividing m, and "
                        + "the smaller prime p. Its last conjunct bounds the ENTIRE Euler raw tail strictly "
                        + "by 2/P. It requires no v_P(m)=1. There are at most floor(R) smaller natural "
                        + "bases; summing once per prime gives 2 floor(R)/P. For an occupied j>=3, "
                        + "max(-g,0)<=referencePrice(X)*log(p), since the raw Euler gain is nonnegative. "
                        + "Summing with all actual multiplicities gives referencePrice(X)*M3(m). "
                        + "Finally call the existing record_third_mass_bound. No exchange theorem or "
                        + "record Euler-tail theorem is reproved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-compact-second-raw-expansion"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherLayerResidual.compact_second_raw_margin"),
                H("The compact-uniform raw margin and its exact root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Put a=sqrt(2), L=log(X), r=sqrt(X), t=r*(a+s/L). secondRawMargin(X,t) is "
                        + "log((1-t^{-3})/(1-t^{-2}))-log(t)/(X L), the exact real extension of the "
                        + "prime second raw margin. For fixed K>=0, |s|<=K, 2K<=a L and t>1, "
                        + "the source proves |X L*secondRawMargin(X,t)+s/a+log(a)| <= "
                        + "(4K^2+2K/a)/L+12L/(a^3 r). The right side depends only on X and the fixed K, "
                        + "and tends to zero. The limiting root is s0=-a log(a)=-log(2)/sqrt(2).")),
                    Paragraph(Text(
                        "For real t>1 set q=1/(t(t+1)). Algebra identifies the Euler ratio as 1+q. "
                        + "Mathlib's logarithm inequalities give q-q^2/2<=log(1+q)<=q; "
                        + "0<=t^{-2}-q<=t^{-3} and q^2<=t^{-4} imply "
                        + "|log(1+q)-t^{-2}|<=3/(2t^3). Set h=s/L and u=a+h. When |h|<=a/2, "
                        + "the exact reciprocal-square remainder is "
                        + "u^{-2}-1/2+h/a=h^2(3a+2h)/(2a u^2), between zero and 4h^2. "
                        + "The elementary log-ratio inequalities give |log(u)-log(a)|<=2|h|/a. "
                        + "Using r^2=X, log(r)=L/2 and u>=a/2 bounds the gain error by 12L/(a^3r). "
                        + "Adding these three errors proves the displayed uniform estimate. "
                        + "It concerns the RAW margin, not the margin divided by log(p)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-complete-second-layer-fixed-tube"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherLayerResidual.finite_actual_second_layer_tube_bound"),
                H("Complete second-layer critical loss in a fixed delta tube"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix 0<delta<=1 before the threshold. Set K=|s0|+1, A=t_X(s0-delta), "
                        + "B=t_X(s0+delta). The finite theorem assumes X>1, n>=1 with antitone actual "
                        + "prime valuations, 2K<=a L, expansion error <=delta/(2a), r<A, and "
                        + "A<Q2<B. It also assumes SEPARATELY |theta(A)-A|<=delta*r/(2L) and "
                        + "|theta(B)-B|<=delta*r/(2L). These are explicit analytic tail conditions; "
                        + "they are not a defect hypothesis or a renamed desired conclusion. It proves "
                        + "0<=r L^3*(actualDefect-C1-D3)<=9 delta^2/a.")),
                    Paragraph(Text(
                        "The compact estimate gives positive raw margin at A and negative raw margin "
                        + "at B. The real raw margin is antitone for t>1. Actual record layer occupancy "
                        + "is exactly p<=Q2, so every p<=A is occupied with nonnegative margin, and "
                        + "every p>=B is missing with nonpositive margin. Both endpoint losses are "
                        + "EXACTLY ZERO even when the endpoint is prime. At p=Q2 the occupied formula "
                        + "applies; a zero-margin coordinate has zero loss in either state. Thus the "
                        + "entire loss is in (A,B). Within the tube its absolute raw margin is at most "
                        + "3delta/(2a X L), using the two endpoint estimates and monotonicity.")),
                    Paragraph(Text(
                        "The weak-endpoint finite set W=primesLE(floor(B)) minus primesLE(floor(A)) "
                        + "contains (A,B). Its log mass is exactly theta(B)-theta(A). The exact width "
                        + "B-A=2delta*r/L and the two separate endpoint errors give log mass "
                        + "<=3delta*r/L. For every p in W, p>A>r, so log(p)>=L/2 and "
                        + "card(W)<=6delta*r/L^2. Multiplying this full prime count by the raw "
                        + "absolute margin gives C2<=9delta^2/(a r L^3). The upper endpoint included "
                        + "in W and lower endpoint excluded from W both have zero loss; no singleton "
                        + "correction is hidden. Finally the literal finite decomposition rewrites "
                        + "C2 as actualDefect-C1-D3."))),
                DescribeRole.Theorem)
        )));
}
