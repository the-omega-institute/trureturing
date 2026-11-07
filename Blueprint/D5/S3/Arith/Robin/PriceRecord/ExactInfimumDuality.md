# Literal objectives and image infima

## Abstract

Exact nested-log envelopes for the genuine real and supported-integer infima.

The finite real and supported-integer envelopes retain the literal objectives and image infima below, with the original public hypotheses and conclusions. BoundaryPrimePrice and OwnClockFixedSupport supply the unchanged local losses and fixed-support objects. No admission, escape registration, freeze, integration or RH conclusion is asserted.

Let S be any finite set of genuine natural primes, with card S>=3 and ell=log(theta S)>=1. Put H=theta S=sum_S log p, lambda=1/(H*ell), b_p=boundary p lambda, and Q=phi S b-baseline S+tangentRemainder H (clock S b). Set G=sum_S integerGap p lambda and g_ell(q)=log(1+log(1+ell*q)/ell). Canonical ActualRobinClockCovariance.g H is definitionally exactly this lambda; the fixed-price identity and integer upper bound explicitly normalize that definition.

Every imported definition is retained literally. admissible S x means x_p>=1 for p in S; clock S x=sum_S x_p log p; terminalCost T=log(log T); phi retains EulerGamma, the nonlinear terminal cost at this vector's clock, and every original benefit. realInfimum S is sInf of {v:R | exists x:N->R, admissible S x and phi S x=v}. integerInfimum S is sInf of {v:R | exists a:N->Z, (for every p in S, 1<=a_p) and phi S (fun p => (a_p:R))=v}. baseline S remains EulerGamma+terminalCost(theta S)+sum_S log(1-p^-1). There is no bounded image, new baseline, alternate objective or assumed optimizer.

## Elementary envelope and exact all-vector argument

For 0<=x<=y, the positive-domain log_div identity and log t<=t-1 give log(1+y)-log(1+x)<=((1+y)/(1+x))-1=(y-x)/(1+x)<=y-x. This consumed helper is used twice to prove the one-Lipschitz inequality for g_ell. More precisely, for 0<=q1<=q2, the inner logarithm increment is at most ell*(q2-q1); division by ell>0 bounds a2-a1 by q2-q1, where ai=log(1+ell*qi)/ell. The outer logarithm increment is at most a2-a1. The same positive-domain monotonicity of log proves g_ell(q1)<=g_ell(q2). All inner logarithms have arguments at least one, each ai is nonnegative, and all outer arguments are at least one.

Take any admissible vector x, without a minimizer, cutoff or sublevel restriction. Put T=clock S x, w=(T-H)/(H*ell) and U=-sum_S log(1-probability p (x_p)). theta_le_clock gives w>=0. The inherited gap_identity_nonnegative supplies U>=0 and delta=phi S x-baseline S=terminalCost T-terminalCost H+U. The inherited terminal_cost_increment and the identity ell*w=(T-H)/H give delta=g_ell(w)+U exactly.

The inherited fixed_price_identity is delta=Q+sum_S priceLoss p lambda (x_p)-tangentRemainder H T. By the literal remainder definition and lambda*(T-H)=w, the remainder equals w-(terminalCost T-terminalCost H). Cancelling with the preceding Euler-factor identity gives Q+sum_S priceLoss=w+U exactly. If C>=0 is paid by the actual price-loss sum, this proves Q+C<=w+U. Since Q>=0, monotonicity and the one-Lipschitz inequality give g_ell(Q+C)<=g_ell(w+U)<=g_ell(w)+U=delta. Monotonicity alone would not justify the second step; the repaired source explicitly consumes the one-Lipschitz proof.

For q>=0 put a=log(1+ell*q)/ell. The canonical logarithm upper bound gives 0<=a<=q. The original canonical CurvatureCorrectedArithmeticSurplus.log_one_add_quadratic, whose statement and proof are unchanged, gives a>=q-ell*q^2/2 and log(1+a)>=a-a^2/2. Since a^2<=q^2, one obtains q-g_ell(q)<=((ell+1)*q^2)/2. The upper logarithm bound also gives g_ell(q)<=a<=q, so 0<=q-g_ell(q). The proof applies to the whole nonnegative ray; no smallness premise occurs.

**Theorem 1.1 (Real infimum: g(Q)<=I<=Q and explicit quadratic error).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ExactInfimumDuality.real_infimum_nested_log_sandwich`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ExactInfimumDuality.real_infimum_nested_log_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With I=realInfimum S-baseline S the complete conclusion is 0<=Q, g_ell(Q)<=I, I<=Q, 0<=Q-I, and Q-I<=((ell+1)*Q^2)/2. The only public assumptions are the original prime support, card S>=3 and ell>=1.

Boundary admissibility is immediate from boundary=max(1,critical). The accepted real_infimum_bounds gives baseline S<=phi S b, and tangent_remainder_nonnegative gives a nonnegative remainder because H and clock S b exceed one; hence Q>=0. For every admissible x, boundary_maximum gives 0<=sum_S priceLoss. Apply the all-vector envelope with C=0. The accepted real_values_nonempty_bdd_below supplies the exact image's conditional-completeness obligations. le_csInf makes g_ell(Q)+baseline S a lower bound on realInfimum S. For the upper bound csInf_le uses the actual boundary vector b in that same image, followed by the nonnegative remainder.

The final error assembly uses both g_ell(Q)<=I and Q-g_ell(Q)<=((ell+1)*Q^2)/2 to derive Q-I<=((ell+1)*Q^2)/2. Nonnegativity of Q-I follows from the independently proved I<=Q.

**Theorem 1.2 (Integer infimum: g(Q+G)<=I<=Q+G on its actual image).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ExactInfimumDuality.integer_infimum_nested_log_sandwich`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ExactInfimumDuality.integer_infimum_nested_log_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With I=integerInfimum S-baseline S the complete conclusion is 0<=Q, 0<=G, g_ell(Q+G)<=I, I<=Q+G, 0<=(Q+G)-I, and (Q+G)-I<=((ell+1)*(Q+G)^2)/2. The public hypotheses and the original integer image are unchanged.

Each integer_gap_bounds at k=1 gives a nonnegative summand, hence G>=0. For an arbitrary admissible integer vector a, its real cast is admissible, and integer_gap_bounds at a_p yields G<=sum_S priceLoss p lambda a_p. Apply the all-vector envelope with C=G. The unchanged integer_values_nonempty_bdd_below supplies the literal integer image's nonemptiness and boundedness below: a_p=1 witnesses nonemptiness, and baseline S<=realInfimum S<=phi S a bounds every image value below. le_csInf on that exact set yields the nested-log lower bound without attainment.

For the upper bound the source directly consumes the public integer_infimum_uniform_sandwich with r=1, projects its .2 and unfolds the canonical lambda. That supplier chooses primewise integer_gap_attained witnesses on the finite subtype p in S, fills off-support coordinates with 1, proves sum_S priceLoss=G, uses the exact identity and the nonnegative tangent remainder, and applies csInf_le to the literal integer image. No nonlinear integer minimizer is assumed or asserted. The final quadratic error uses q=Q+G>=0 and combines g_ell(q)<=I with q-g_ell(q)<=((ell+1)*q^2)/2. Actual local lets Q and G and an explicit change retain these names during assembly.

## Canonical logarithm and uniform suppliers

The original CurvatureCorrectedArithmeticSurplus.log_one_add_quadratic is exposed by removing only private, preserving its exact type and proof. Both new modules import and consume it directly; the unfrozen duplicate is deleted. In RealInfimumUniformDuality only terminal_cost_increment, gap_identity_nonnegative, integer_values_nonempty_bdd_below and fixed_price_identity are exposed for cross-module use. The original public theorem telescopes and literal integerInfimum definition are preserved.

Live consumers are nested_log_error for the canonical quadratic supplier; fixed_price_envelope_pointwise for terminal_cost_increment, gap_identity_nonnegative and fixed_price_identity; and integer_lower_nested_log for integer_values_nonempty_bdd_below. The uniform module also consumes the original quadratic supplier internally. Every local helper leads to one or both public results. No copied scalar proof, unused forwarding wrapper, admitted statement or new axiom is introduced. The same identities and inequalities apply on the full admissible domain.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ExactInfimumDuality.integer_infimum_nested_log_sandwich`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ExactInfimumDuality.real_infimum_nested_log_sandwich`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus](CurvatureCorrectedArithmeticSurplus.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RealInfimumUniformDuality](RealInfimumUniformDuality.md)
