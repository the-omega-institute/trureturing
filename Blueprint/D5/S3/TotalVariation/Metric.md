# Metric Laws and Variational Characterization for Finite Total Variation

## Abstract

Finite total variation satisfies the metric laws, the probability unit bound, and an attained event-gap characterization.

**Theorem 1.1 (Total variation is unconditionally nonnegative).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\0\le \operatorname{TV}(p, q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Metric.total_variation_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before this module, the TotalVariation bucket contained only the Pinsker module. Pinsker bounded total variation by relative entropy, measured in nats, but did not establish a single basic metric property of total variation, not even nonnegativity.

The present declaration supplies that first property for arbitrary finite real mass functions. No sign or normalization hypothesis is present: each coordinate contributes an absolute value, the finite sum is nonnegative, and multiplication by one half preserves the order.

**Theorem 1.2 (Total variation separates finite real mass functions).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\\operatorname{TV}(p, q)=0 \Leftrightarrow p=q.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Metric.total_variation_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vanishing is equivalent to equality of the two functions. If the half-L1 sum vanishes, the finite sum of nonnegative absolute differences is zero; hence every coordinate difference is zero. Conversely, substituting equal functions makes every summand vanish.

This separation result is again unconditional. It depends on the zero set of the absolute value and on a finite sum of nonnegative terms, not on an interpretation of p and q as probability vectors.

**Theorem 1.3 (Total variation is symmetric).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\\operatorname{TV}(p, q)=\operatorname{TV}(q, p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Metric.total_variation_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Symmetry follows coordinatewise from the symmetry of absolute subtraction. Exchanging p and q changes each signed difference to its negative and leaves its absolute value, the finite sum, and the factor one half unchanged.

Accordingly, symmetry requires neither nonnegative coordinates nor equal total mass. It is a property of the absolute-value expression itself.

**Theorem 1.4 (Total variation satisfies the triangle inequality).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q, r: \iota\to \mathbb{R},\\\operatorname{TV}(p, r)\le \operatorname{TV}(p, q)+\operatorname{TV}(q, r).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Metric.total_variation_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar triangle inequality is applied to p(i)-r(i), decomposed as p(i)-q(i) plus q(i)-r(i), and is then summed over the finite index type. Distributivity of finite sums and the nonnegative factor one half give the displayed inequality.

Nonnegativity, separation, symmetry, and the triangle inequality therefore hold with no assumptions beyond finiteness. Structurally, all four are properties of absolute value and finite sums rather than properties of probability. Together they make total variation a genuine metric on finite real mass functions, although this module proves the laws directly and does not register a MetricSpace instance.

**Theorem 1.5 (Probability vectors have total variation at most one).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \land\\((\forall i, 0\le q(i)) \land \sum_{i}q(i)=1) \Rightarrow\\\operatorname{TV}(p, q)\le 1.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Metric.total_variation_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit bound is the first result in this module that uses probability hypotheses. Coordinatewise nonnegativity gives |p(i)-q(i)| <= p(i)+q(i); normalization makes the sum on the right equal to two, and the defining factor one half yields the bound one.

Both parts of each probability-vector hypothesis are necessary to this argument as formalized: p and q are nonnegative and each has total mass one. These assumptions are absent from the four metric laws and are stronger than the equal-mass premise used by the variational theorem below.

**Theorem 1.6 (Total variation is the greatest attained event gap).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\\sum_{i}p(i)=\sum_{i}q(i) \Rightarrow\\\operatorname{IsGreatest}(\operatorname{range}(A: \operatorname{Finset}(\iota)\mapsto \Vert (\sum_{i\in A}p(i))-\sum_{i\in A}q(i) \Vert),\\\operatorname{TV}(p, q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Metric.total_variation_eq_sup_event_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the result with the principal interpretive content: total variation is the largest probability-mass gap achievable over events. The statement applies more generally to arbitrary finite real mass functions whose total masses are equal. It requires neither coordinatewise nonnegativity nor normalization to one.

The theorem deliberately uses IsGreatest rather than a literal supremum. Membership in the stated range records, in the theorem's own type, that a concrete event attains total variation; the upper-bound field records that no event has a larger gap. A literal iSup formulation would introduce conditionally-complete-lattice machinery and obscure attainment. A Finset.sup' fold over the powerset would require a separate nonemptiness witness and hide the maximum behind fold infrastructure.

The attaining event is the dominance set {i | q(i) <= p(i)}. On this event the signed excess is nonnegative and equals total variation by the frozen pinning identity total_variation_eq_sum_positive from the Pinsker module. For an arbitrary event, discarding its negative contributions bounds its signed gap by the same dominance-set excess; applying the argument in the reverse order controls the opposite sign and hence the absolute gap.

The upper-bound field is not vacuous. For two disjoint unit point masses on Bool, total variation is one, whereas the empty event has gap zero and, more tellingly, the whole index set also has gap zero because the total masses are equal. Thus the maximum is emphatically not attained by every event. More generally, for any unequal equal-mass pair, the whole event has zero gap and cannot attain the positive maximum. This Bool witness was compiled independently of the formal proof.

With these declarations in place, later total-variation developments can invoke the basic metric properties rather than re-derive them, and Pinsker's divergence bound in nats now sits inside a metric structure rather than standing alone. No reverse bound of Bretagnolle-Huber type, measure-theoretic analogue, completeness theorem, or topological statement about the induced metric is claimed. Nor is a MetricSpace instance registered: the metric properties are proved, not packaged.

## References

- Truth anchor: `D5/S3/TotalVariation/Metric.total_variation_comm`
- Truth anchor: `D5/S3/TotalVariation/Metric.total_variation_eq_sup_event_gap`
- Truth anchor: `D5/S3/TotalVariation/Metric.total_variation_eq_zero_iff`
- Truth anchor: `D5/S3/TotalVariation/Metric.total_variation_le_one`
- Truth anchor: `D5/S3/TotalVariation/Metric.total_variation_nonneg`
- Truth anchor: `D5/S3/TotalVariation/Metric.total_variation_triangle`
- Dependency: [D5/S3/TotalVariation/Pinsker](Pinsker.md)
