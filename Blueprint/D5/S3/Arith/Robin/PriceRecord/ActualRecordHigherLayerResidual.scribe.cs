using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualRecordHigherLayerResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete actual prime-layer loss and the residual beyond the first layer.",
        H("The literal residual and one threshold for all record prices"),
        Blocks(
            Paragraph(Text(
                "The complete residual beyond the first layer combines the finite higher-layer loss "
                + "bound, the compact second-margin expansion, and the second-layer fixed-tube estimate. "
                + "The one threshold is chosen before the original integer and its arbitrary positive "
                + "record price. The complete first-layer bound remains open.")),
            Paragraph(Text(
                "Exact target, retained without weakening: for every epsilon>0 there exists X0>1, chosen "
                + "before every natural m>=2 and every real mu>0, such that if the ORIGINAL objective at mu "
                + "strictly exceeds its value at EVERY natural 0<k<m and X=log(m)>=X0, then "
                + "0<=sqrt(X)*log(X)^3*(actualDefect(X,m)-completeFirstLayerLoss(X,m))<epsilon. "
                + "Here referencePrice(X)=1/(X log(X)) defines the pressure clock. The original arbitrary mu "
                + "is never identified with that price. No defect bound, RH, prime short-window premise, "
                + "support cap, or exponent cap is an assumption.")),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-record-uniform-critical-nonfirst-residual"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualRecordHigherLayerResidual.actual_record_critical_residual"),
                H("One own-X threshold before all literal records and prices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every epsilon>0 the theorem chooses ONE X0>1 before every integer "
                        + "m>=2 and arbitrary original price mu>0 satisfying the literal strict objective "
                        + "comparison with EACH positive predecessor k<m. If X=log(m)>=X0, its conclusion "
                        + "is exactly 0<=sqrt(X)*log(X)^3*(actualDefect(X,m)-completeFirstLayerLoss(X,m)) "
                        + "<epsilon. The original mu is never replaced by referencePrice(X).")),
                    Paragraph(Text(
                        "G1 fixes delta>0 first. tube_endpoint_limits gives separately, for each fixed s, "
                        + "t_X(s)->infinity, t_X(s)/sqrt(X)->sqrt(2), and log(X)/log(t_X(s))->2. "
                        + "theta_error_at_tube applies global theta_error_log_power(1), multiplying its "
                        + "normalized error by these two ratios. Thus (log(X)/sqrt(X))*(theta(t)-t)->0 "
                        + "at EACH endpoint s=s0-delta and s=s0+delta. fixed_tube_eventually converts "
                        + "their separate delta/2 tails into exactly the two finite theta inequalities. "
                        + "The explicit secondExpansionError tends to zero by Mathlib log-power/rpow "
                        + "asymptotics, while the endpoint geometry gives sqrt(X)<A. No shrinking delta(X), "
                        + "interval PNT premise, or assumed cancellation of errors is used.")),
                    Paragraph(Text(
                        "The only new own-clock helper is appended inside FullArithmeticCorrectionSecondOrder. "
                        + "record_second_own_clock_limit uses the ORIGINAL unit_sqrt(unit_inv(record_mass_limits.2.2)), "
                        + "second_layer_limits, second_mul_unit and relative_clocks. It transports Q2/sqrt(P) "
                        + "to Q2/sqrt(X) and log(P) to log(X), obtaining coefficient -log(2)/sqrt(2). "
                        + "This helper has the actual same-delivery residual proof as its consumer. No standalone "
                        + "own-log module or three-conclusion wrapper is imported or retained.")),
                    Paragraph(Text(
                        "G2 uses the existing record_log_envelope X<=P*log(4P^2) to prove P escape on ALL "
                        + "record pairs filtered by comap(X,atTop). The existing record_mass_limits supplies "
                        + "X/P->1; the original record_layer_ratio at j=3 supplies Q3^3/P->3. Choose "
                        + "R=(X*log(X)/log(2))^(1/3). The real power identities give EXACTLY "
                        + "X*log(X)=log(2)*R^3. Eventually X/2<=P<=2X and log(4P^2)<=4log(X). "
                        + "The standard limit log(X)/X^(1/4)->0 and X^(1/4)>=8 imply "
                        + "R,Q3<=X^(5/12). Consequently 1<=R<=sqrt(X)<X/2<=P. The finite higher bound "
                        + "applies without any valuation assumption at P or artificial support cap.")),
                    Paragraph(Text(
                        "The COMPLETE normalized finite higher envelope is squeezed between zero and "
                        + "8*log(X)^3/X^(1/12), tending to zero by the existing log-power/rpow asymptotic. "
                        + "Indeed 2R/P<=4X^(5/12)/X, and Q3*log(4P^2)/(X log(X))<=4X^(5/12)/X. "
                        + "The identity sqrt(X)*X^(5/12)*X^(1/12)=X gives the displayed normalization. "
                        + "This deliberately coarse envelope suffices; no reproof of the owner's rate calculus "
                        + "or infinite summation is involved.")),
                    Paragraph(Text(
                        "G3 chooses delta=min(1,sqrt(sqrt(2)*epsilon/36)) BEFORE all thresholds, so "
                        + "9delta^2/sqrt(2)<=epsilon/4. The own-X Q2 coefficient gives A<Q2<B. "
                        + "Intersect this tail with G1 and the complete higher-loss epsilon/2 tail. "
                        + "Antitone actual valuations come from price_record_prime_structure. Apply the finite "
                        + "second-layer theorem and combine its nonnegative loss with the complete higher loss "
                        + "by the exact defect split. The total is <epsilon/4+epsilon/2<epsilon. "
                        + "eventually_comap followed by eventually_atTop extracts one B; X0=max(B,2) "
                        + "precedes m and mu. There is no fixed-price or subsequence restriction.")),
                    Paragraph(Text(
                        "The mathematical theorem retains the exact literal record telescope and complete "
                        + "loss. Its four-slot source audit remains separate: the final-law negative-family "
                        + "variation and sensitivity use arbitrarily large literal records, while actual "
                        + "observational dependence on a lawful scoped reconstruction, exact sourceSelection "
                        + "and current producer binding still require evidence. The existing validated compact "
                        + "raw-margin registration is preserved. No complete registration is asserted for "
                        + "this uniform residual or the newly visible owner suppliers."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "An ordinary sharper estimate also follows from the same finite bound. Choose R=(X L/log(2))^(1/3). The existing same-integer "
                + "record_mass_limits gives X/P->1 uniformly, and record_log_envelope gives "
                + "X<=P log(4P^2), so X->infinity forces P->infinity before arbitrary prices. "
                + "FixedLayerRigidity at j=3 gives Q3^3/P->3; eventually X/2<=P<=2X, Q3<=2X^(1/3), "
                + "L>=2, log(4P^2)<=4L, M3<=8X^(1/3)L, R>=1 and R<P. The finite higher theorem "
                + "therefore yields r L^3 D3 <= "
                + "4/(log(2)^(1/3))*X^(-1/6)*L^(10/3)+8X^(-1/6)*L^3. "
                + "Both terms tend to zero by the existing log-power versus positive-real-power "
                + "asymptotic. This sharper envelope counts the whole missing tail once per prime; "
                + "the Pro pair-count logarithmic factor is unnecessary.")),
            Paragraph(Text("5040 application and first-layer boundary")),
            Paragraph(Text(
                "The record theorem's conditional 5040 application uses only the existing "
                + "uniform_actual_least_crossing_price_record and uniform_actual_height_escape, with "
                + "Tepsilon=max(Trecord,Tescape(X0)) chosen before eta,T,m. The former gives a positive "
                + "original price and the strict objective comparison with EVERY positive predecessor; "
                + "the latter and divisor_log_le_log give log(m)>X0. No named binding wrapper is needed. "
                + "This is conditional on being an actual least crossing and constructs none. It "
                + "asserts no Robin sign or RH conclusion. First-layer boundedness "
                + "sqrt(X)*log(X)^3*C1=O(1) remains explicitly OPEN after full residual isolation. Neither the finite estimates nor the ordinary Pro argument "
                + "changes that boundary."))
        )));
}
