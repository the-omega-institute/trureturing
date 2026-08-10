# Log-Sum Inequality and Joint Convexity on General Support

## Abstract

The finite log-sum inequality and joint convexity of real-valued KL divergence under discrete absolute continuity.

**Theorem 1.1 (Coordinatewise relative entropy dominates its aggregate).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall a, b: \iota\to \mathbb{R},\\((\forall i, 0\le a(i)) \land (\forall i, 0\le b(i)) \land\\(\forall i, b(i)=0 \Rightarrow a(i)=0)) \Rightarrow\\(\sum _{i} a(i)) \log (\frac{\sum _{i} a(i)}{\sum _{i} b(i)})\le \\\sum _{i} a(i) \log (\frac{a(i)}{b(i)}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LogSumInequality.log_sum_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and b be nonnegative mass vectors on a finite type, with discrete absolute continuity: b(i) = 0 implies a(i) = 0. The theorem says that aggregating the two vectors before comparing them can only understate their relative entropy. The sum of the coordinatewise comparisons dominates the comparison of the total masses. This scalar inequality is the engine behind the convexity and data-processing consequences of finite classical divergence.

The absolute-continuity hypothesis is indispensable: without it, the inequality is false, not merely unproved or vacuous. On Bool, take a(i) = 1 at both coordinates and take b(false) = 1, b(true) = 0. The left side aggregates to 2 log 2, which is strictly positive. The right side is zero: the nonzero-denominator coordinate contributes log 1 = 0, while Lean's conventions x / 0 = 0 and Real.log 0 = 0 make the other coordinate contribute 1 log 0 = 0 rather than the positive infinity it carries in extended-real relative entropy. Thus the unguarded statement asserts 2 log 2 <= 0. This counterexample was compiled by the author in the formal module and compiled independently by the caller.

The value assigned at a zero-denominator coordinate is therefore a Lean convention, not a mathematical claim that the corresponding relative entropy is finite or zero. Any theorem ranging over such coordinates must retain b(i) = 0 implies a(i) = 0 if its divergence terminology is to have the intended mathematical meaning. Strict positivity of b is not required. The support condition suffices, and together with nonnegativity it makes a zero total mass for b force a zero total mass for a.

When the total mass of b is positive, the proof normalizes b, applies finite Jensen convexity to InformationTheory.klFun, and cancels the affine correction in klFun to obtain the displayed logarithmic terms. The zero-total branch is discharged by the support condition. No normalization of either mass vector is assumed.

**Theorem 1.2 (Finite KL divergence is jointly convex on general support).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p_{1}, p_{2}, q_{1}, q_{2}: \iota\to \mathbb{R}, t\in \mathbb{R},\\((0\le t \land t\le 1) \land\\(\forall i, 0\le p_{1}(i) \land 0\le p_{2}(i) \land 0\le q_{1}(i) \land 0\le q_{2}(i)) \land\\(\forall i, (q_{1}(i)=0 \Rightarrow p_{1}(i)=0) \land (q_{2}(i)=0 \Rightarrow p_{2}(i)=0))) \Rightarrow\\D(t p_{1}+(1-t) p_{2}\Vert t q_{1}+(1-t) q_{2})\le \\t D(p_{1}\Vert q_{1})+(1-t) D(p_{2}\Vert q_{2}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LogSumInequality.kl_divergence_joint_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each coordinate i, apply the two-term log-sum inequality on Bool with a = (t p1(i), (1-t) p2(i)) and b = (t q1(i), (1-t) q2(i)). The bounds 0 <= t <= 1 make both mixing weights nonnegative, while the two original support conditions supply the support condition for the scaled pairs, including at the endpoint weights. Summing the resulting scalar inequality over i gives the displayed joint-convexity bound.

Beyond the two log-sum inputs' nonnegativity and absolute-continuity hypotheses, only the mixing range 0 <= t <= 1 is added. Probability normalization is not required. Joint convexity is therefore a coordinatewise corollary here, not an independent argument: the load-bearing half of the module is the log-sum inequality.

DivergenceSupport is registered for finite classical-divergence identities and bounds under general-support and absolute-continuity conventions. This theorem lies exactly in that regime, which is why it belongs here rather than in the TotalVariation bucket. The module does not characterize equality, provide a continuous or measure-theoretic analogue, establish convexity for other distances, or generalize the claim to Renyi divergence. All logarithms are natural, so the units are nats.

## References

- Truth anchor: `D5/S3/DivergenceSupport/LogSumInequality.kl_divergence_joint_convex`
- Truth anchor: `D5/S3/DivergenceSupport/LogSumInequality.log_sum_inequality`
- Dependency: [D5/S3/Divergence/ClassicalDPI](../Divergence/ClassicalDPI.md)
