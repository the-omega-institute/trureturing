# A normalized finite-sum root estimate

## Abstract

Nonnegative finite inverse-power sums control the norm of a complex root by its argument.

**Theorem 1.1 (The argument-dependent estimate).**

$$\forall (J:\operatorname{Type})[Fintype\left(J\right)],\forall a \in J \to \operatorname{Real},\; \forall k \in J \to \operatorname{Nat},\; \forall a0 \in \operatorname{Real},\; \forall z \in \operatorname{Complex},\; \left(\forall i \in J,\; 0 \le a\left(i\right)\right) \Rightarrow \left(0 < a0 \Rightarrow \left(1 < \left\lVert z \right\rVert \Rightarrow \left((a0:\operatorname{Complex})+\sum_{(i:J)}(a\left(i\right):\operatorname{Complex})\cdot (z^{-1})^{k\left(i\right)} = 0 \Rightarrow \left\lVert z \right\rVert \le (\frac{\sum_{(i:J)}a\left(i\right)}{a0})^{\frac{\left|\operatorname{Complex}.\operatorname{arg}\left(z\right)\right|}{\operatorname{Real}.\operatorname{pi}}}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/DegreeRoots/EscapeWitness.normalized_escape_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be nonnegative real weights on a finite type, k natural exponents, and a0 a positive real constant. If a0 plus the weighted inverse powers of z vanishes and the norm of z exceeds one, then its norm is at most the ratio of total weight to a0, raised to |Complex.arg z|/Real.pi. For positive argument, put lam=Real.log ‖z‖/Complex.arg z and take the real part after multiplication by 1+lam·Complex.I. The estimate Real.exp(−lam·t)(Real.cos t+lam·Real.sin t)≥−Real.exp(−lam·Real.pi) for lam>0 and t≥0 bounds each summand. Complex conjugation handles negative argument; a positive constant and nonnegative weights exclude argument zero.

## References

- Truth anchor: `D5/S3/Zeros/DegreeRoots/EscapeWitness.normalized_escape_bound`
