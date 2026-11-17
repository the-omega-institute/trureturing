# The full original two-layer budget

## Abstract

Greatest feasible global optimizers and exact full original two-layer budgets.

All logarithms are real natural logarithms. For a natural integer m and real c, write a=optimalLayerCount(c,2), v=v_2(m), r=v-a with natural subtraction, and I=Icc(a+1,v). The entire original tail I includes equality layers: a is the strict canonical cutoff, so its next equality layer is excluded from the prefix and retained with zero loss. Define h=h2(m,c)=r log(2), J=J2(m,c)=sum_{j in I}(c-goldenLayerMarginal(2,j))log(2), U=ordinary2tailReward(m,c)=sum_{j in I}goldenLayerMarginal(2,j)log(2), and n=deleted2tailInteger(m,c)=m/2^r using natural division. The literal library resource objective is denoted by F_t(n).

**Theorem 1.1 (Transfer the literal objective between two prices).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.objective_price_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.objective_price_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real mu,s and positive natural m,C, F_s(C)-F_s(m)=F_mu(C)-F_mu(m)+(s-mu)log(m/C). The original objective and original integers are retained; neither price needs to be positive. The full-tail arbitrary-bracket comparison consumes this identity at the actual greatest feasible optimizer.

**Theorem 1.2 (The reward and deficit of the same full tail).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.reward_deficit_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.reward_deficit_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m and real c, ordinary2tailReward(m,c)=c*h2(m,c)-J2(m,c). The finite interval is the complete original tail, with natural truncated subtraction. No positivity or occupied-tail assumption is required. The arbitrary-bracket full-tail comparison uses this identity together with actual integer deletion and the existing reward bound.

**Theorem 1.3 (Construct the greatest feasible global optimizer).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.greatest_feasible_global_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.greatest_feasible_global_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real s>0 and natural m with strictInteger(s)<=m<=maximalInteger(s), if m is not globally resource-optimal at s, there exists a natural C with GlobalBudgetGap(s,m,C). This means 1<=C, strictInteger(s)<=C<m<maximalInteger(s), C is globally optimal at s, every positive globally optimal n<=m satisfies n<=C, and C divides maximalInteger(s). Put y=log(m/C). Then y>0, there exists an omitted prime q with v_q(C)<v_q(maximalInteger(s)), and s*y*exp(y)<1.

For EVERY prime q with this omitted-valuation inequality, its next marginal equals s, q*C remains globally optimal, m<q*C, y<log(q), and s*q*log(q)<1. No number of equality primes is bounded or assumed. The finite set of actual global optimizers in Icc(1,m) contains strictInteger(s); its natural-order maximum constructs C. At each omitted prime, the threshold criterion and the maximal weak valuation give equality of the next marginal to s. Inserting that layer preserves the objective, and maximality forces the product above m. The first-layer logarithm bound then yields s*q*log(q)<1 and the exponential bound.

**Theorem 1.4 (Delete the entire original tail at any comparison price).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_deletion_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_deletion_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m>=1, every real c with a<=v, and EVERY real comparison price t, the deleted integer n satisfies 1<=n, v_2(n)=a, n*2^r=m, and F_t(m)-F_t(n)=(c-t)*h-J. There is no positivity assumption on c or t. The prime-factorization division identity leaves every other prime valuation unchanged. The literal local objective difference is the full finite sum over Icc(a+1,v), derived from the existing local_eq_layer_sum. In particular the identity applies at both the original record price mu and the bracket price s.

**Theorem 1.5 (The exact ordinary reward of the same tail).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_reward_telescope`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_reward_telescope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m and real c with a<=v, U=log((2-(2 inverse)^v)/(2-(2 inverse)^a)). The powers have natural exponents and the inverse is real. No m>=1 or c>0 hypothesis is needed. The finite local telescope at price zero and positivity of its geometric numerators prove the equality, including a=v.

**Theorem 1.6 (Bound the full reward by its first tail layer).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_reward_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_reward_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m and real c>0 with a<=v, U<2*(goldenLayerMarginal(2,a+1)*log(2)) and U<2*c*log(2). Put x=(2 inverse)^(a+1) and z=(2 inverse)^(v+1). The exact reward is log((1-z)/(1-x))<log(1/(1-x)). The strict inequality 1-x<(1-x/2)^2 bounds it by twice the first tail reward. Strict canonical cutoff membership bounds the next marginal by c. No layer is removed from U, h or J, and the empty-tail case is included.

**Theorem 1.7 (A necessary forbidden-window budget for a full predecessor record).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_forbidden_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_forbidden_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m,k be arbitrary naturals, m>=1 and T=log(m)>1. Let mu>0 be any original price for which F_mu(n)<F_mu(m) for EVERY positive n<m. Assume 1<=k<=v_2(m) and goldenLayerMarginal(2,k)<c, where c=ownPrice(m)=1/(T*log(T)). Let s>0 be ANY price satisfying the literal bracket strictInteger(s)<=m<=maximalInteger(s) and the EXPLICIT hypothesis c<=s. Then there exists C with GlobalBudgetGap(s,m,C) and FullTailBudgetRestriction(mu,s,m,C). The theorem neither supplies a bad occupied layer nor proves c<=s for every record. The layer k may be anywhere in the original valuation interval, and no bank-occupancy premise occurs.

With the same original m, its own c, the same full tail, and y=log(m/C), the restriction asserts a<v, h>0, J>0, mu<c, mu<s, 1<=n<m, J<(c-mu)*h, and J+(s-c)*h<(s-mu)*y. It also asserts J/(c-mu)<=(J+(s-c)*h)/(s-mu), (J+(s-c)*h)/(s-mu)<y, and J/(c-mu)<y<log(T). For EVERY omitted equality prime q of C in maximalInteger(s), q<T and log(q)<log(T). Finally U<2*c*log(2), h<y+2*log(2), and the REAL power 2^r<4*T.

Deleting the full tail at mu gives its strict record budget and mu<c. At s the positive tail loss and c<=s rule out global optimality of m. Construct C by the greatest-feasible theorem and compare its objective with the deleted integer. The strict original record inequality at C gives the stronger budget after changing price. The identity U=c*h-J and full reward bound give the tail-length bound. Each omitted prime satisfies s*q*log(q)<1; c<=s and monotonicity of t*log(t) give q<T. Exponentiating the length bound and y<log(T) yields 2^r<4*T.

These are necessary restrictions under the stated hypotheses. They do not establish the original eight bank modes 2,3,4,5,6,8,9,12 in both directions with prescribed b, delta and h, all fees and full payment. Those simultaneous bank obligations, Robin beyond 5040 and RH remain open. No Six Exponentials, Baker-Harman-Pintz, tie-cardinality or analytic endpoint supplier is assumed.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_deletion_identity`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_forbidden_budget`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_reward_bound`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.full_original2tail_reward_telescope`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.greatest_feasible_global_gap`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.objective_price_difference`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap.reward_deficit_identity`
- Dependency: [D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone](../../GoldenResource/FirstLayerMarginalAntitone.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceSupremum](../../GoldenResource/GoldenResourceSupremum.md)
- Dependency: [D5/S3/Arith/Robin/ActualGlobalBracketing](../ActualGlobalBracketing.md)
