# Škorić's truncated binomial mean

## Abstract

The cap-normalized mean of an integer binomial row truncated to a positive cap is nonincreasing.

**Definition 1.1 (f).**

$$\forall x \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{f}\left(x, r\right) = \frac{1}{(r: \mathbb{R})} \cdot \frac{\sum_{w\in \operatorname{Finset.range}\left(r + 1\right)} (w: \mathbb{R}) \cdot (\operatorname{Nat.choose}\left(x, w\right): \mathbb{R})}{\sum_{w\in \operatorname{Finset.range}\left(r + 1\right)} (\operatorname{Nat.choose}\left(x, w\right): \mathbb{R})}$$

*Formalization.* `D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.f` (`✓ std3`).

*Citation.* Boris Škorić (2021). *Quantum digital signatures with smaller public keys*. DOI: [10.26421/QIC21.11-12-4](https://doi.org/10.26421/QIC21.11-12-4). URL: <https://arxiv.org/abs/2012.15493v2>.

*Commentary.*

Conjecture 1: “Let $\operatorname{f}\left(x, r\right)$ be defined as” (equation (35)). “The function $\operatorname{f}\left(x, r\right)$ is decreasing in $r$.”

Škorić, §6.2, Conjecture 1, equation (35), journal p.966. The displayed formula is the source's definition of f. Both finite sums include w=0 and w=r. The upper argument x and cap r are natural numbers; Nat.choose is the ordinary binomial coefficient, cast to ℝ before summation. Division is in ℝ. Comparisons use positive caps, so the totalized value at r=0 is outside them.

**Definition 1.2 (claim).**

$$claim \Leftrightarrow \left(\forall x \in \mathbb{N},\; 2 \le x \Rightarrow \left(\forall r \in \mathbb{N},\; 1 \le r \Rightarrow \left(\forall s \in \mathbb{N},\; r < s \Rightarrow \left(2 \cdot s \le x \Rightarrow \operatorname{f}\left(x, s\right) \le \operatorname{f}\left(x, r\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.claim` (`✓ std3`).

*Citation.* Boris Škorić (2021). *Quantum digital signatures with smaller public keys*. DOI: [10.26421/QIC21.11-12-4](https://doi.org/10.26421/QIC21.11-12-4). URL: <https://arxiv.org/abs/2012.15493v2>.

*Commentary.*

Conjecture 1: “Let $\operatorname{f}\left(x, r\right)$ be defined as” (equation (35)). “The function $\operatorname{f}\left(x, r\right)$ is decreasing in $r$.”

Škorić, §6.2, Conjecture 1, equation (35), journal p.966. Here x ranges over integers at least two, and r and s are positive integer caps with r<s and 2s≤x. Decrease is expressed as nonincrease, f(x,s)≤f(x,r). The restriction 2s≤x expresses the source's r≤x/2 at the larger cap, without integer division.

**Theorem 1.3 (result).**

$$\forall x \in \mathbb{N},\; 2 \le x \Rightarrow \left(\forall r \in \mathbb{N},\; 1 \le r \Rightarrow \left(\forall s \in \mathbb{N},\; r < s \Rightarrow \left(2 \cdot s \le x \Rightarrow \operatorname{f}\left(x, s\right) \le \operatorname{f}\left(x, r\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.result` (`✓ std3`). ∎

*Resolves.* `Problems/skoric-truncated-binomial-mean` (proved) by `D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"skoric-truncated-binomial-mean","declaration_gid":"D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Boris Škorić (2021). *Quantum digital signatures with smaller public keys*. DOI: [10.26421/QIC21.11-12-4](https://doi.org/10.26421/QIC21.11-12-4). URL: <https://arxiv.org/abs/2012.15493v2>.

*Commentary.*

For a positive row satisfying k·a(k)²≥(k+1)·a(k−1)·a(k+1), the adjacent difference of normalized means has a positive numerator. Symmetrizing the product of the two partial sums partitions it into convolution blocks. Monotonicity of the weighted adjacent ratios controls every high block; the low block with index sum one contributes a(0)·a(1)>0. Chaining adjacent comparisons and using the binomial recurrence proves the stated comparison. This proves the scalar assertion used by source Propositions 1 and 2; their other hypotheses and the protocol's security analysis are separate questions.

## References

- Truth anchor: `D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.claim`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.f`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.result`
