# Original Robin interval transfer

## Abstract

Original Robin margins transfer across actual optimizer intervals; all-price endpoint estimates remain explicit.

Write W(n)=log(sigma(n)/n) and Phi(A)=gamma+log(log(A)). The original margin is Phi(log(n))-W(n). The same objective, sigma and original integers are retained.

**Theorem 1.1 (Transfer between actual same-price optimizers).**

Lean statement: `D5/S3/Arith/Robin/ActualRobinInterval.optimizer_interval_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualRobinInterval.optimizer_interval_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive q and original optimizers B,U at q with 3<=B<=n<=U, the margin at n is at least the convex combination of the endpoint margins, and strictly greater in the genuine interior. The weight t is (log(n)-log(B))/(log(U)-log(B)), with the source's zero convention at coincident endpoints. Objective optimality proves the W chord bound. Strict log-log concavity is proved rather than supplied as a final hypothesis; endpoint signs are not assumed in this transfer theorem.

**Theorem 1.2 (Every integer through an actual maximal endpoint).**

Lean statement: `D5/S3/Arith/Robin/ActualRobinInterval.original_robin_through_maximal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualRobinInterval.original_robin_through_maximal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any positive q0. Assume positive original Robin margins for every actual strict or maximal endpoint above 5040 at every price q>=q0. Then every natural integer 5040<n<=maximalInteger(q0) satisfies sigma(n)<exp(gamma)*n*log(log(n)). Natural-order coverage constructs the interval. If its price is below q0, actual prime-layer divisibility forces maximalInteger(q0)<=strictInteger(q)<=n<=maximalInteger(q0), so n equals the checked upper endpoint. Otherwise the two supplied margins and interval concavity apply. The remaining finite boundary is computed as 55440 inside the proof, using the same q11 identification as the full global reduction. The upper-price margins remain explicit hypotheses of this general theorem.

**Theorem 1.3 (The exact unpaid all-price obligation).**

Lean statement: `D5/S3/Arith/Robin/ActualRobinInterval.global_margin_iff_unpaid_estimates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualRobinInterval.global_margin_iff_unpaid_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive original margins for every natural n>5040 are equivalent to EndpointRobinEstimates: for every positive real q with strictInteger(q)>5040, both strictInteger(q) and maximalInteger(q) have positive original margin. The constructed coverage supplies the reverse implication. Its finite branch identifies the chosen boundary price as the first layer at prime 11, with strict product 5040 and maximal product 55440, and invokes the existing finite Robin theorem there. No separate finite-boundary premise remains. This equivalence does not prove EndpointRobinEstimates.

**Theorem 1.4 (Consume endpoint estimates in the original inequality).**

Lean statement: `D5/S3/Arith/Robin/ActualRobinInterval.global_original_robin_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualRobinInterval.global_original_robin_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assuming EndpointRobinEstimates, every natural n>5040 satisfies sigma(n)<exp(gamma)*n*log(log(n)). The final logarithm/exponential transport pays its positivity conditions and retains the original sigma, integer factor and iterated logarithm. This conditional reduction proves neither the all-price endpoint estimates nor RH.

## Finite actual-pressure continuation

This is source implementation support for the existing Robin finite consumer. The private Lean continuation is integrated in this same owner; its exact verification evidence is separate from this mathematical narrative. The persistent packet has 1330 rational cells, 2660 endpoint tests, 664579 purported primes and 665320 candidate layers through 10000000; those are packet claims and Python evidence, not kernel acceptance. The finite theorem and the full Robin/RH goal remain open.

Retain the actual pressure P(q)=sup over n>=1 of goldenResourceObjective(q,n), q(x)=1/(x log(x)), and epsilon(x)=1/(100 sqrt(x) log(x)). The target is P(q(x))<=gamma+log(log(x))-1/log(x)-epsilon(x) for every real x in [1849/100,10000000]. The implementation uses the existing ActualTwoPriceDefect carrier and positive-price boundedness; it introduces no proxy pressure.

For 1<u<=x<=v and w>1, assume both endpoint values P(q(t))+w q(t), t=u,v, are at most B=gamma+log(log(w))-epsilon(u). For fixed n, the translated objective is log(sum over d|n of 1/d)+(w-log(n))q. If its coefficient is nonnegative, compare q(x) to q(u); otherwise compare it to q(v). The actual endpoint suprema bound the two integer objectives. The objective set contains n=1, so csSup_le gives P(q(x))+w q(x)<=B. No interpolation denominator, global pressure convexity, differentiability, optimizer continuity or inverse price map is needed. The same proof applies when u=v.

RestrictedDivisorStrictInventory.loglog_tangent already proves the strict tangent at x!=w for ActualRobinClockCovariance.g(x)=1/(x log(x)). Definition transport identifies this with the actual price. At x=w the tangent equality is immediate. Combine it with x q(x)=1/log(x) and epsilon(x)<=epsilon(u); the latter follows from positive increasing sqrt and log factors. This gives the literal full cell bound, including all equality-price activation ties. There is no new weak-tangent or convexity module.

For prime p and a>=1, B(p,a)=sum from i=0 to a-1 of p^(i+1). The geometric identity B(p,a)(p-1)=p(p^a-1) identifies log(p)*goldenLayerMarginal(p,a) with log(1+1/B(p,a)). The existing supremum formula is transported by symmetry of its objective-set equality. Every actual active layer is embedded into the supplied finite layer set. Each gain is bounded by max(dUpper-qLower*logpLower,0); adding nonnegative conservative terms permits ambiguous activation and zero-gain ties without identifying the envelope prefix with the true active set.

GoldenLayerMarginalDecay.golden_layer_marginal_le_inv_pow suffices to exclude layers whenever p^a log(p)>=X log(X), since their marginal is then <=q(X)<=q(x) for 1<x<=X. For omitted primes p>=X use p^a>=p and log monotonicity. For represented primes use the recorded first excluded exponent and monotonicity of p^a. The implementation derives support containment from prime completeness, enumeration of every earlier layer, directed prime/X log bounds and exact rational cutoff comparisons. These concrete obligations have not been proved for the packet.

The prefix calculation requires the prefix to lie in the full candidate set, every included envelope gain to be nonnegative, every omitted gain to be nonpositive, and exact D and L sums. It then proves the envelope sum equals D-qLower*L. Directed endpoint logarithms prove qLower<=q(t)<=qUpper; the positive center permits P(q(t))+w q(t)<=D-qLower*L+w qUpper. A positive rational square lower bound and log lower bound enclose epsilon(u). The existing HarmonicGammaUpperTail.eulerMascheroni_lower_64 supplies 5772156649/10^10<gamma. Directed log-log lower bounds and the packet's rational margins then imply the two endpoint conditions.

A finite grid-cover induction selects an interval containing any real point between its first and last vertices, including exact vertices and singleton cells. The root fixes the endpoints to 1849/100 and 10000000, derives both endpoint conditions for the selected cell from the primitive obligations, and applies the cell proof. The grid is indexed by shared vertices, so a decoder must still identify every packet row's u,v with consecutive vertices; its coverage, endpoints, domain and margin checks remain explicit.

Outstanding work is concrete: a source-bound packet decoder and rational data realization; forward inclusion of every actual prime below X in the supplied set; all exponent-cutoff and layer-enumeration checks; directed fixed-point log recurrence/range reduction and square inequalities; all prefix signs, sums and rational margins; and complete contiguous row coverage. No assumed validator or endpoint-pressure hypothesis replaces these checks. Retained-row primality and an exact census are not premises: extra candidates are harmless when the actual conservative endpoint sums meet the required margins. No data were regenerated. Canonical scoped kernel, axiom and Scribe checks do not themselves settle admission; PR20756 retains first delivery priority and no standalone SOURCE, Reg, freeze, independent delivery, tail or RH claim is made.

## Directed logarithm input correspondence

The mathematical recurrence belongs to GoldenResource.DirectedLogarithmBounds. This is only its consuming continuation in ActualRobinInterval; the ended endpoint/cell/tangent implementation remains the supplier. The Lean file is a SAME-SOURCE splice after fp_finite_consumer, with the new arithmetic import added at the top. It exposes no standalone accepted finite theorem.

FPLogEvaluation(x) stores natural n,d,k, a natural integer pair, d>0, d*2^k<=n<d*2^(k+1), x=n/d as a rational identity, a positive lower integer, and pair=totalLogBounds(n,d,k). Total correctness of the actual recurrence derives its real logarithm bracket; no successful-run field or semantic logarithm assumption remains. The total accessor is the getD result of the original Option algorithm at fuel 100, whose default is proved unreachable via uniform success by step 33. Layer records similarly identify their exact stored pair with totalLayerBounds. Both total-correctness suppliers are consumed in fp_finite_consumer_directed. FPLogInputs records the corresponding field identities for lp,du, the X cutoff bound, every endpoint log interval, the u lower log, the center lower log, and its subsequent log. These arithmetic identities replace the old semantic logarithm hypotheses on the path to fp_finite_consumer. A full instance for the actual packet is still absent.

The natural owner now supplies totalBounds width<=100 at the actual first stop j<=33, totalLogTwo width<=200, totalLogBounds width<=200k+100 (<=4700 on n/d<=10000000), and totalLayerBounds width<=100. Public predecessor statement telescopes and all recorded integers remain unchanged. The finite splice derives per-layer real upper error between 0 and 100/S, then inducts over an arbitrary actual layer list L to obtain total error at most 100*length(L)/S, counting multiplicity. It requires each listed entry to be a prime layer with positive exponent and its exact recorded totalLayerBounds identity. It does not infer these facts from unread tables.

fp_finite_consumer_directed remains the same private consumer path and retains every nonlogarithmic hypothesis. Its private conclusion is strengthened to the conjunction of the original all-real pressure inequality and the general layer-list error budget for lists drawn from its recorded T. The singleton budget supplies hd to the original fp_finite_consumer; the general budget is returned alongside that pressure conclusion for use on complete lists or prefixes. No gratuitous theorem for a fixed census length, detached checker framework, new success hypothesis or concrete full-packet instance is introduced.

First cell: u numerator 1849, v numerator 1867, denominator 100, midpoint 3716/200=929/50. u log pair is (2917230045399033478909702117244,2917230045399033478909702117416); v log pair is (2926917957553631246002738595450,2926917957553631246002738595622); center log pair is (2922085733385692458672045959162,2922085733385692458672045959334). All are divided by S=10^30. Taking logBounds of the center's LOWER INTEGER over S gives (1072297653550266923187835307253,1072297653550266923187835307316); the recorded log-log lower integer is exactly its first component, not a log of the center upper bound.

Last cell: u numerator 995838609, v numerator 1000000000, denominator 100, midpoint 1995838609/200. u log pair is (16113925577274391947387699142285,16113925577274391947387699143198); v log pair is (16118095650958319788125940182365,16118095650958319788125940183279); center log pair is (16116012787804097067940727576424,16116012787804097067940727577338). Logarithm of the center LOWER INTEGER over S gives (2779813360813775913593635940837,2779813360813775913593635941001). The packet uses its first component for log-log. No other cell record or full prime/layer table was used here.

The retained concrete total-accessor data identities and first/last primitive records are source proof scripts using decide. All original sample integers and input denominators are preserved. Their kernel evidence must be read from the exact current scoped report, rather than inferred from the stored integers. The strict parameter condition is derived from each explicit integer range witness, so it is never inferred at the excluded value z=1/3. The full table's exact data identities, data-to-Finset/field realization and all nonlogarithmic primitive obligations remain unpaid. No full FPLogInputs instance, census, layer enumeration, margin or interval result is claimed. No packet was regenerated or expanded; native verification is separate from admission and preserves PR20756 first delivery priority. No acceptance, freeze, registration, full finite, tail or RH receipt follows from these sources.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualRobinInterval.global_margin_iff_unpaid_estimates`
- Truth anchor: `D5/S3/Arith/Robin/ActualRobinInterval.global_original_robin_reduction`
- Truth anchor: `D5/S3/Arith/Robin/ActualRobinInterval.optimizer_interval_transfer`
- Truth anchor: `D5/S3/Arith/Robin/ActualRobinInterval.original_robin_through_maximal`
- Dependency: [D5/S3/Arith/GoldenLayerMarginalDecay](../GoldenLayerMarginalDecay.md)
- Dependency: [D5/S3/Arith/GoldenResource/DirectedLogarithmBounds](../GoldenResource/DirectedLogarithmBounds.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceSupremum](../GoldenResource/GoldenResourceSupremum.md)
- Dependency: [D5/S3/Arith/GoldenResource/HarmonicGammaUpperTail](../GoldenResource/HarmonicGammaUpperTail.md)
- Dependency: [D5/S3/Arith/GoldenResource/ThresholdChainReduction](../GoldenResource/ThresholdChainReduction.md)
- Dependency: [D5/S3/Arith/Robin/ActualGlobalBracketing](ActualGlobalBracketing.md)
- Dependency: [D5/S3/Arith/Robin/FewDistinctPrimes](FewDistinctPrimes.md)
- Dependency: [D5/S3/Arith/Robin/LogarithmBounds](LogarithmBounds.md)
