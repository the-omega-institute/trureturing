# Nonnegativity of Finite Entropy

## Abstract

Finite Shannon and conditional entropy are nonnegative in nats, completing the finite Shannon-entropy bracket.

**Theorem 1.1 (Finite Shannon entropy is nonnegative).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \Rightarrow\\0\le \operatorname{shannonEntropy}(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/EntropyNonneg.shannon_entropy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This result supplies the lower bound that the entropy bucket was missing. The sibling maximum-entropy theorem already proves H <= log card on a finite nonempty alphabet, but without this theorem nothing ruled out negative entropy for a legitimate distribution. Together, the two bounds place its Shannon entropy in [0, log card].

Each summand is Mathlib's Real.negMulLog, which is nonnegative on the unit interval. The proof applies Real.negMulLog_nonneg term by term and sums the resulting inequalities; it follows the library-before-proof principle rather than re-deriving the scalar lemma. The upper endpoint p(i) <= 1 is derived, not assumed: nonnegativity gives p(i) <= sum_j p(j), and normalization identifies that sum with 1.

Normalization is genuinely required for this lower bound. Without a unit sum, a single mass of 2 has Real.negMulLog 2 < 0, so the entropy can be negative. This differs from several sibling identities in this bucket, which need only nonnegativity; the unit-sum hypothesis here is therefore substantive rather than gratuitous. The units are nats because Real.negMulLog uses the natural logarithm.

No equality condition is claimed. In particular, this theorem does not prove that entropy vanishes exactly on point masses, and it says nothing about strict positivity for non-degenerate distributions.

**Theorem 1.2 (Finite conditional entropy is nonnegative).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\(\forall i, j, 0\le p(i,j)) \Rightarrow\\0\le \operatorname{conditionalEntropy}(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/EntropyNonneg.conditional_entropy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditional entropy is a sum of marginal weights times the Shannon entropies of conditional slices. For every nonzero marginal, the corresponding quotient slice is nonnegative and has unit sum, so the preceding Shannon bound applies. This normalization is derived from the marginal definition; no global unit-sum hypothesis is imposed on the joint. The outer marginal weights are nonnegative because they are finite sums of nonnegative joint masses.

A zero marginal is the essential exceptional case. Its conditional slice is defined by quotienting by zero and is not a distribution, so the per-slice Shannon bound does not apply. The proof handles this by cases: the outer weight is zero, and its entire conditional-entropy term vanishes. No positivity is assumed anywhere.

The conclusion is nonnegativity of finite conditional entropy in nats. As in the Shannon statement, no equality condition is claimed: this theorem neither characterizes zero conditional entropy nor proves strict positivity for non-degenerate conditional laws.

## References

- Truth anchor: `D5/S3/Entropy/EntropyNonneg.conditional_entropy_nonneg`
- Truth anchor: `D5/S3/Entropy/EntropyNonneg.shannon_entropy_nonneg`
- Dependency: [D5/S3/Entropy/ConditionalEntropy](ConditionalEntropy.md)
