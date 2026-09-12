# Baez-Duarte Q Bounds

## Abstract

The original unsigned Q series bounds the actual Baez-Duarte coefficients unconditionally, with an explicit all-index half-power estimate.

**Definition 1.1 (The original unsigned series).**

$$\forall k \in \mathbb{N},\; Q\left(k\right)=\sum_{n=0}^{\infty} \frac{1}{(n+1)^{2}} (1-\frac{1}{(n+1)^{2}})^{k}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baezDuarteQ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Q is exactly the source series with positive integer index shifted by one. The original n equals one term is retained, including zero to the zeroth power.

**Theorem 1.2 (Summability at every index).**

$$\forall k \in \mathbb{N},\; Summable\left((n\mapsto\frac{1}{(n+1)^{2}} (1-\frac{1}{(n+1)^{2}})^{k})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baez_duarte_q_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Nonnegative original summands have bounded partial sums by the finite split at cutoff one. No convergence hypothesis is imposed.

**Theorem 1.3 (Nonnegativity).**

$$\forall k \in \mathbb{N},\; 0\le Q\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baez_duarte_q_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Every original summand is nonnegative; the closed interval endpoints are retained.

**Theorem 1.4 (The all-index bound).**

$$\forall k \in \mathbb{N},\; Q\left(k\right)\le \frac{3}{sqrt\left(k+1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baez_duarte_q_le_three_div_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The private live escape finite_q_split_bound bounds every partial sum through M by N divided by k plus one, plus one divided by N, for every natural k, M and positive natural N, including M less than N. Its geometric_weight_bound prerequisite proves t times the kth power of one minus t is at most one divided by k plus one on the entire closed unit interval, using the finite geometric identity. The tail uses mathlib's inverse-square interval bound. The live Q proof applies that finite split with N equal to Nat.sqrt(k+1); it is an intermediate estimate, not a restatement of the final conclusion. The explicit constant three, shifted all-index estimate and finite split are repo-derived refinements of Lemma 2.1, not literal statements in the source.

**Theorem 1.5 (Comparison with the actual coefficients).**

$$\forall k \in \mathbb{N},\; \left|c\left(k\right)\right|\le Q\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.abs_baez_duarte_le_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

c denotes the imported D5.S3.Weil.RieszBaezDuarte.baezDuarte, whose existing baez_duarte_hasSum_moebius is the sole arithmetic owner. Its signed sum is compared with the original Q using the integer Mobius absolute bound. The arithmetic owner's private q is not this Q.

**Theorem 1.6 (Unconditional coefficient decay).**

$$\forall k \in \mathbb{N},\; \left|c\left(k\right)\right|\le \frac{3}{sqrt\left(k+1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.abs_baez_duarte_le_three_div_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

This thin companion consumes the actual-c comparison and Q bound. Remark 1.1 and equations (2.7)-(2.8) acknowledge the source of the unconditional half-power result.

**Theorem 1.7 (The positive-index power form).**

$$\forall k \in \mathbb{N},\; 1\le k\Rightarrow Q\left(k\right)\le 3 k^{-\frac{1}{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baez_duarte_q_le_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

For every positive index this is a thin consequence of the shifted bound; the all-index theorem continues to control index zero.

**Theorem 1.8 (The actual-c power form).**

$$\forall k \in \mathbb{N},\; 1\le k\Rightarrow \left|c\left(k\right)\right|\le 3 k^{-\frac{1}{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.abs_baez_duarte_le_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

This companion consumes the actual-c comparison and the positive-index Q estimate.

**Theorem 1.9 (The full zero-index prefix).**

$$Q\left(0\right)\le 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baez_duarte_q_zero_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The finite split at cutoff one also gives Q at zero at most two. The original first summand is one, so it cannot be discarded.

Source standing is user-requested formalization of known literature with repo-derived quantitative refinements and the typed Library acknowledgement. Utility none applies to general analytic estimates and their thin companions; no bounded enumeration, checker, numerical reduction or certified finite instance is introduced. Neither RH direction nor the original Newton identity is proved. The future absolute double-series consumer of Q times P remains unimplemented. The Library note retains the epsilon versus epsilon/2 discrepancy, the printed positive 3/4 on page five, and the Lemma 2.2 cross-reference distinction.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.abs_baez_duarte_le_q`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.abs_baez_duarte_le_rpow`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.abs_baez_duarte_le_three_div_sqrt`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baezDuarteQ`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baez_duarte_q_le_rpow`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baez_duarte_q_le_three_div_sqrt`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baez_duarte_q_nonneg`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baez_duarte_q_summable`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.baez_duarte_q_zero_le_two`
- Dependency: [D5/S3/Weil/ZetaBridge/RieszBaezDuarte](../../Weil/ZetaBridge/RieszBaezDuarte.md)
