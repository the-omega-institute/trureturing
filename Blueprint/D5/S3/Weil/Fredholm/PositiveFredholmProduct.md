# Positive Fredholm Product Completion

## Abstract

Weighted reciprocal-square summability makes the positive square-folded spectral product converge and increase on the nonnegative axis.

**Theorem 1.1 (The positive square-folded spectral product converges monotonically).**

$$\begin{aligned}\forall iota: Type, gamma: iota \to \mathbb{R}, m: iota \to \mathbb{N},\\F(x) = \prod_{i\in iota} {1 + x / {gamma(i)}^2}^{m(i)},\\{\forall i\in iota, 0 < gamma(i)} \land \operatorname{Summable}\left(\lambda i \mapsto m(i) / {gamma(i)}^2\right) \Rightarrow {\forall x\in \mathbb{R}, 0 \leq x \Rightarrow \operatorname{Multipliable}\left(\lambda i \mapsto {1 + x / {gamma(i)}^2}^{m(i)}\right)} \land F(0) = 1 \land {\forall x\in \mathbb{R}, 0 \leq x \Rightarrow 1 \leq F(x)} \land \operatorname{MonotoneOn}\left(F, \operatorname{Ici}\left(0\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Fredholm/PositiveFredholmProduct.positive_fredholm_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive ordinates gamma and their natural-number multiplicities are abstract inputs. The only analytic input is summability of the multiplicity-weighted reciprocal squares. Expanding each multiplicity as a finite fiber turns this into summability of the individual nonnegative increments.

Pinned Mathlib's logarithmic infinite-product criterion proves multipliability for every nonnegative x. The exponential formula for the product then gives the lower bound one and carries termwise monotonicity to the completed product. At x = 0 every factor is one, so the product is normalized.

The accompanying Lean module also supplies a nonempty Basel witness with gamma_i = i + 1 and unit multiplicity, including convergence at x = 1, and proves that multiplicity m_i = i makes the required weighted series diverge.

The Riemann-hypothesis description of the ordinates and the zero-density theorem producing the summability premise remain external inputs. No countable trace-class operator or Fredholm determinant is claimed, because the pinned library does not provide the required operator API.

## References

- Truth anchor: `D5/S3/Weil/Fredholm/PositiveFredholmProduct.positive_fredholm_completion`
