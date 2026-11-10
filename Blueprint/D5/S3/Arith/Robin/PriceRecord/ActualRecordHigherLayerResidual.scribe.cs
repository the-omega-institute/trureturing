using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualRecordHigherLayerResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete actual prime-layer loss and the residual beyond the first layer.",
        H("The literal residual, its finite estimates, and the remaining source obligation"),
        Blocks(
            Paragraph(Text(
                "SOURCE PREPARATION ONLY: UNCOMPILED_UNACCEPTED. This packet contains three proposed finite "
                + "Lean estimates with full proof bodies and faithful typed Reg source mirrors. The full "
                + "uniform residual theorem is NOT declared: the uniform threshold and limiting-envelope "
                + "assembly remains an exact source gap. The complete ordinary deduction below explains "
                + "that gap without promoting it to a compiled theorem. Scribe has not been emitted or built, "
                + "and no Reg registration is declared_validated.")),
            Paragraph(Text(
                "Exact target, retained without weakening: for every epsilon>0 there exists X0>1, chosen "
                + "before every natural m>=2 and every real mu>0, such that if the ORIGINAL objective at mu "
                + "strictly exceeds its value at EVERY natural 0<k<m and X=log(m)>=X0, then "
                + "0<=sqrt(X)*log(X)^3*(actualDefect(X,m)-completeFirstLayerLoss(X,m))<epsilon. "
                + "Here referencePrice(X)=1/(X log(X)) defines the pressure clock. The original arbitrary mu "
                + "is never identified with that price. No defect bound, RH, prime short-window premise, "
                + "support cap, or exponent cap is an assumption.")),
            H("Exact finite objects and completeness"),
            Paragraph(Text(
                "Use the library's actualPressure=sup of goldenResourceObjective(referencePrice(X),n) "
                + "over all n>=1, and its actualDefect=that pressure minus the objective of the same original "
                + "integer. pressureOptimizer(X) chooses the minimal-count optimizer supplied by "
                + "optimal_layer_count_spec. lossPrimes is the union of that optimizer's primeFactors and "
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
                        + "the proposed theorem gives 0<=D3, D3<=2 floor(R)/P+referencePrice(X)*M3(m), "
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
            H("Ordinary full uniform deduction and the exact missing Lean assembly"),
            Paragraph(Text(
                "Choose epsilon>0 and delta=min(1,sqrt(a*epsilon/36)) FIRST. Then "
                + "9delta^2/a<=epsilon/4. Consume the first conjunct of the FULL proposed "
                + "ActualRecordOwnLogSecondLayer.actual_record_own_log_second_layer at error delta; "
                + "do not introduce a named projection. It supplies |L*(Q2/r-a)-s0|<delta uniformly "
                + "before m and mu, hence A<Q2<B. This own-log module and its three original owner "
                + "visibility changes are UNCOMPILED_UNACCEPTED dependencies of the full deduction. "
                + "They are not dependencies of the three finite theorems in the present Lean file, "
                + "and the original private rate calculus is not duplicated.")),
            Paragraph(Text(
                "For fixed delta the deterministic endpoints have A/r,B/r->a and "
                + "log(A)/L,log(B)/L->1/2. Eventually r<A and B<=2a*r, and the explicit compact "
                + "remainder is <=delta/(2a). Apply the existing global theta_error_log_power(1) "
                + "with eta=delta/(8a). At BOTH endpoints separately, y/log(y)<=4a*r/L eventually, "
                + "so |theta(y)-y|<=delta*r/(2L). This derives precisely the finite tube hypotheses "
                + "from the global PNT. There is no short-prime assumption and no uniformity in a "
                + "simultaneously shrinking delta(X).")),
            Paragraph(Text(
                "For the higher estimate choose R=(X L/log(2))^(1/3). The existing same-integer "
                + "record_mass_limits gives X/P->1 uniformly, and record_log_envelope gives "
                + "X<=P log(4P^2), so X->infinity forces P->infinity before arbitrary prices. "
                + "FixedLayerRigidity at j=3 gives Q3^3/P->3; eventually X/2<=P<=2X, Q3<=2X^(1/3), "
                + "L>=2, log(4P^2)<=4L, M3<=8X^(1/3)L, R>=1 and R<P. The finite higher theorem "
                + "therefore yields r L^3 D3 <= "
                + "4/(log(2)^(1/3))*X^(-1/6)*L^(10/3)+8X^(-1/6)*L^3. "
                + "Both terms tend to zero by the existing log-power versus positive-real-power "
                + "asymptotic. This sharper envelope counts the whole missing tail once per prime; "
                + "the Pro pair-count logarithmic factor is unnecessary.")),
            Paragraph(Text(
                "Take a deterministic threshold making that higher envelope <epsilon/2 and intersect "
                + "it with the finitely many fixed-delta analytic tails, the own-log Q2 tail and the "
                + "uniform record-regime tail. The maximum is one X0>1 BEFORE m and mu. The complete "
                + "finite identity then gives 0<=r L^3*(actualDefect-C1)=r L^3*C2+r L^3*D3 "
                + "<epsilon/4+epsilon/2<epsilon. A subtype of ALL literal record pairs filtered by "
                + "comap(log(m),atTop) expresses the same quantifiers without a fixed-price or "
                + "subsequence restriction. A bottom filter would only make a tail statement vacuous; "
                + "existing arbitrarily_large_price_records and P<=m in fact provide own-X "
                + "nonvacuity by taking P>=exp(T).")),
            Paragraph(Text(
                "EXACT SOURCE GAP: the present Lean file does not yet prove the deterministic eventual "
                + "remainder and two-endpoint theta conditions, does not yet form the record subtype "
                + "and prove its P-regime and normalized higher-envelope limit, and does not yet "
                + "perform the fixed-delta epsilon/max-threshold assembly. Thus the full literal target "
                + "has an ordinary proof from the stated suppliers and finite source proposals, but "
                + "does NOT have a complete Lean proof in this packet. Every finite proof body also "
                + "requires later native elaboration repair as needed. Each of its three public "
                + "types has a faithful source-law/readout Reg mirror; whole-family variation, "
                + "sensitivity, dependence, sourceSelection and binding evidence remain unprovided. "
                + "No historical owner Reg scope or judge was changed.")),
            H("5040 application and first-layer boundary"),
            Paragraph(Text(
                "Once the record theorem is actually proved, its 5040 application uses only the existing "
                + "uniform_actual_least_crossing_price_record and uniform_actual_height_escape, with "
                + "Tepsilon=max(Trecord,Tescape(X0)) chosen before eta,T,m. The former gives a positive "
                + "original price and the strict objective comparison with EVERY positive predecessor; "
                + "the latter and divisor_log_le_log give log(m)>X0. No named binding wrapper is needed. "
                + "This is conditional on being an actual least crossing and constructs none. It "
                + "asserts no Robin sign or RH conclusion. First-layer boundedness "
                + "sqrt(X)*log(X)^3*C1=O(1) remains explicitly OPEN even if full residual isolation "
                + "is later accepted. Neither finite source preparation nor the ordinary Pro proof "
                + "changes that boundary."))
        )));
}
