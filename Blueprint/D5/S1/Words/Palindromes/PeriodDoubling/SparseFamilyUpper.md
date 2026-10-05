# Sparse Family Upper Bounds

## Abstract

Uniform upper bounds for both sparse-family endpoints.

**Theorem 1.1 (Diagonal and off-diagonal upper bounds).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall eps \in \mathbb{N},\; \left(\left(\left(\left(0 < a \land \operatorname{mod}\left(a, 2\right) = 1\right) \land \operatorname{mod}\left(b, 2\right) = 1\right) \land \operatorname{Nat.sub}\left(2 \cdot a, 1\right) \le b\right) \land eps \le 1\right) \Rightarrow \operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(\operatorname{sum}\left(\operatorname{range}\left(a\right), \lambda s:\mathbb{N} \mapsto 2^{2 \cdot b + 0 + 2 + 3 \cdot s}\right) + \operatorname{sum}\left(\operatorname{range}\left(b\right), \lambda j:\mathbb{N} \mapsto 2^{2 \cdot j + 1}\right) + eps\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right) \le \operatorname{ite}\left(b = \operatorname{Nat.sub}\left(2 \cdot a, 1\right), 3 \cdot a, a + b + eps\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SparseFamilyUpper.sparse_family_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive odd a, odd b at least 2a minus one, and epsilon zero or one, repeated six-cut reductions produce the displayed uniform bound. At b equal to 2a minus one both endpoints have at most 3a factors. At larger odd b the bounds are a+b and a+b+1. The diagonal terminal uses a three-factor construction at an even exponent; the other terminal uses the alternating-tail reduction. Nat.sub denotes truncated natural subtraction, mod denotes natural remainder, and val denotes the natural value of a finite index.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SparseFamilyUpper.sparse_family_upper`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/AlternatingTailUpper](AlternatingTailUpper.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SparseBlockUpperSteps](SparseBlockUpperSteps.md)
