# Finite-History Soft Control

## Abstract

Finite-horizon entropy-regularized control on the original stochastic support, for all feasible path laws and all history policies.

Let X be a finite state type, R a nonnegative transition matrix with every row summing to one, c the real cost of each supported edge, g a real terminal cost, and tau > 0. A fixed initial state supplies nonemptiness when needed. Zero entries of R are allowed. Only successors y with R(x,y) > 0 enter the path space; values assigned to c outside that support play no role.

A path of remaining horizon n is the empty history when n = 0, and otherwise a supported successor together with a path of length n - 1. Its reference mass is the product of the original R entries, and its total cost is the sum of the edge costs plus g at the endpoint. For any nonnegative normalized path law p, the objective is its expected total cost plus tau times KL(p || reference). The support restriction makes the reference strictly positive on this actual path space, while p may vanish.

A policy is a full rooted tree of normalized distributions on supported successors, with a separate continuation after every history. Thus the policy quantifier includes history dependence and unreachable histories. The product law, its reference counterpart, the path cost, and conditional KL all use the same R, c, g, tau and horizon. At horizon zero the path and policy carriers are singletons, reference and policy masses are one, the cost is g, and KL is zero.

The source uses remaining horizon: value(0) = g and value(n + 1) = soft(value(n)), where soft(v)(x) = -tau log(sum_y R(x,y) exp(-(c(x,y) + v(y))/tau)). The original time convention is V_t = value(H - t), D_t = hard(H - t), for t <= H. Control consists of choosing a successor probability distribution within the reference support and paying its KL cost; an additional prescribed action set is outside these assumptions.

**Lemma 1.1 (Supported paths exist at every finite horizon).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.path_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.path_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Row normalization and nonnegativity force at least one positive reference successor at every state. Choose such a successor and apply induction to its continuation; pairing them constructs a path. The zero horizon uses the unique empty history. No global strict positivity of R is required.

**Lemma 1.2 (The original product reference is positive on supported paths).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.reference_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.reference_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each selected edge has strictly positive R weight by the definition of a supported successor. Induction multiplies that weight by the positive reference mass of the tail. This positivity concerns feasible paths, and allows zero entries elsewhere in the transition matrix.

**Lemma 1.3 (Every history policy induces a probability law).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.law_prob`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.law_prob` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a successor node the sum over the dependent path space is the sum over supported successors of the sums over their tails. Tail normalization reduces each inner sum to one; normalization of the chosen row then gives total mass one. All factors are nonnegative, including rows with zero controlled masses.

**Lemma 1.4 (The reference path law is normalized).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.reference_prob`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.reference_prob` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same dependent sum decomposition applies to the original R products. Removing the zero R entries preserves each row sum, so tail normalization and the stochastic row identity give a normalized reference path law. This is the original reference of the path objective.

**Lemma 1.5 (Reference continuations realize the original reference law).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.referencePolicy_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.referencePolicy_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reference policy chooses the original supported R row at every history. Its product law equals the original reference path mass as a function on the complete feasible path space. The recursive equality also provides a normalized continuation to use at histories assigned zero mass by another law.

**Lemma 1.6 (Every feasible path probability law is a history policy law).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.law_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.law_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an arbitrary nonnegative normalized function p on the whole supported path space. Sum p over each first-successor branch to obtain a normalized marginal q. When q(y) > 0, divide that branch by q(y), factor its normalized tail by induction, and use the resulting continuation. When q(y) = 0, nonnegativity forces every mass in that branch to vanish; use the reference continuation there. Multiplication by q(y) recovers p in both cases.

At horizon zero normalization on the one-point path space forces p = 1. Thus factorization is derived for arbitrary feasible path laws, rather than assumed or restricted to laws supplied by a policy. The construction imposes no positivity condition on p and places no condition on how an unreachable continuation is chosen beyond feasibility.

**Lemma 1.7 (Path KL equals the actual history-weighted conditional KL sum).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.actual_conditional_KL_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.actual_conditional_KL_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the first-step marginal and each continuation law on the dependent tail spaces. The exact zero-support DPI identity, applied to the first-successor indicator channel, splits the product-path KL into the row KL plus the row-weighted tail KL. Induction repeats this identity along the actual policy tree. Zero controlled mass contributes zero, so unreachable histories cause no omitted term or division hypothesis.

The conditional decomposition reuses `D5/S3/DivergenceSupport/ZeroSupportDPI.classical_dpi_identity_zero_support` on the actual first-step indicator channel. The row lower bound reuses `D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg` after normalization of the exponential row. These are existing finite KL results; the history construction and induction connect them to the path objective.

**Lemma 1.8 (The soft value bounds every history-policy objective).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.all_history_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.all_history_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a supported row q and continuation value v, the exponential row star_v(y) = R(x,y) exp(-(c(x,y) + v(y) - soft(v)(x))/tau) is normalized and positive. Expanding its logarithm gives expected(c + v) + tau KL(q || R) = soft(v)(x) + tau KL(q || star_v). KL nonnegativity gives the row minimum.

The conditional KL split and the finite expected-cost split decompose the actual path objective into that row term and weighted continuation objectives. The induction hypothesis bounds each continuation, and its nonnegative row weight preserves the inequality even when that weight is zero. This proves the lower bound for the complete history-policy class, with no optimizer assumption.

**Lemma 1.9 (The exponential Markov policy attains the path minimum).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.optimal_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.optimal_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose star_value(n) at a node with n + 1 remaining steps, and recursively choose the same optimal continuation construction at its successor. It depends only on the current state and remaining time. In original time notation it is Q_t*(x,y) = R(x,y) exp(-(c(x,y) + V_(t+1)(y) - V_t(x))/tau). The normalized exponential row is an actual policy row.

Induction turns every continuation objective into its value. The row identity then has KL(star || star) = 0 and gives equality with the soft value. Together with all_history_bound and law_factorization, this shows that V_0(x) is the attained minimum over every feasible path probability law as well as over every history policy. For an arbitrary path law, factorization identifies its path objective with the objective of the constructed policy; the optimal policy law supplies the minimizing law.

The exponential change of variables z_t(x) = exp(-V_t(x)/tau) converts the same recurrence into z_t(x) = sum_y K_tau(x,y) z_(t+1)(y), with K_tau(x,y) = R(x,y) exp(-c(x,y)/tau). Terminal data are z_H = exp(-g/tau). This is a finite-horizon linear recursion.

The same soft operator is monotone and satisfies soft(v + a) = soft(v) + a for a constant a. If every |v(y) - w(y)| <= a with a >= 0, the exponential summands are bounded by the corresponding factors exp(a/tau) and exp(-a/tau); positivity of the partition and the logarithm give |soft(v)(x) - soft(w)(x)| <= a. Taking the uniform bound on the finite state space gives nonexpansion. These algebraic consequences use the same supported partition and temperature.

**Lemma 1.10 (The supported soft minimum has a sharp reference-mass bound).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.soft_hard_row`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.soft_hard_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let hardRow(v)(x) be the attained minimum of c(x,y) + v(y) over supported successors. Let rmin be the smallest positive R entry over the entire finite support graph; the argument x0 in rmin supplies a state and hence a nonempty positive-edge set. Row stochasticity gives 0 < rmin <= 1.

Every summand is at most R(x,y) exp(-hardRow/tau), so the partition is at most exp(-hardRow/tau). At a successor attaining the supported hard minimum, its R weight is at least rmin, so the same partition is at least rmin exp(-hardRow/tau). Taking -tau times the logarithm yields hardRow <= soft <= hardRow + tau log(1/rmin). The minimum, the reference weight and both bounds belong to the same row and support graph.

**Lemma 1.11 (The hard-minimum error accumulates over the remaining horizon).**

Lean statement: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.accumulated_hard_min_error`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.accumulated_hard_min_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hard recursion starts from the same terminal cost g and applies the supported hard minimum. Induction combines the row estimate with monotonicity and constant translation of the soft operator. After n remaining steps, for every state x, 0 <= value(n)(x) - hard(n)(x) <= n tau log(1/rmin). The conclusion is uniform over all states and includes n = 0 with equality.

With n = H - t this is exactly 0 <= V_t(x) - D_t(x) <= (H - t) tau log(1/rmin), for t <= H. R, c, g and tau are held fixed in both recursions. The result is about a finite horizon on a stochastic reference support; it supplies no long-time entropy-pressure or cycle-mean conclusion.

## References

- Truth anchor: `D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg`
- Truth anchor: `D5/S3/DivergenceSupport/ZeroSupportDPI.classical_dpi_identity_zero_support`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.accumulated_hard_min_error`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.actual_conditional_KL_chain`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.all_history_bound`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.law_factorization`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.law_prob`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.optimal_attains`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.path_nonempty`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.referencePolicy_law`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.reference_pos`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.reference_prob`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/FiniteHistorySoftControl.soft_hard_row`
- Dependency: [D5/S3/Divergence/GibbsEquality](../../Divergence/GibbsEquality.md)
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](../../Divergence/GrandmotherTheorem.md)
- Dependency: [D5/S3/DivergenceSupport/ZeroSupportDPI](../../DivergenceSupport/ZeroSupportDPI.md)
