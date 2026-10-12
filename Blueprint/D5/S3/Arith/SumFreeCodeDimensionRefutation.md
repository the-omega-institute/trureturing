# Sum-Free Functions with Different Code Dimensions

## Abstract

First-order sum-freedom on the ternary plane does not determine the dimension of the code obtained by adjoining function coordinates to Reed–Muller rows.

**Definition 1.1 (Ternary coordinate space).**

$$\forall n \in \mathrm{Nat},\; \operatorname{V}\left(n\right) = \left(\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(3\right)\right)$$

*Formalization.* `D5/S3/Arith/SumFreeCodeDimensionRefutation.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The points are n-tuples over the field with three elements.

**Definition 1.2 (Higher-order sum-freedom).**

$$\forall n \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; \forall f \in \operatorname{V}\left(n\right) \to \operatorname{V}\left(n\right),\; \operatorname{SumFree}\left(s, f\right) \Leftrightarrow \left(\forall a \in \operatorname{V}\left(n\right),\; \forall u \in \operatorname{Fin}\left(s\right) \to \operatorname{V}\left(n\right),\; \operatorname{LinearIndependent}\left(\operatorname{ZMod}\left(3\right), u\right) \Rightarrow \sum_{c \in \operatorname{Fin}\left(s\right) \to \operatorname{ZMod}\left(3\right)} \operatorname{f}\left(a + \sum_{i \in \operatorname{Fin}\left(s\right)} \operatorname{c}\left(i\right) \cdot \operatorname{u}\left(i\right)\right) \ne 0\right)$$

*Formalization.* `D5/S3/Arith/SumFreeCodeDimensionRefutation.SumFree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A linearly independent family of s directions parametrizes an affine s-plane without repetitions. The sum of the function over each such plane must be nonzero.

**Definition 1.3 (Reed–Muller monomial indices).**

$$\forall n \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; \operatorname{Monomials}\left(n, s\right) = \{e \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(3\right) | \sum_{i \in \operatorname{Fin}\left(n\right)} \operatorname{val}\left(\operatorname{e}\left(i\right)\right) \le 2 \cdot s - 1\}$$

*Formalization.* `D5/S3/Arith/SumFreeCodeDimensionRefutation.Monomials` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each exponent is at most two and the total degree is at most 2s minus one. The evaluation vectors span the corresponding Reed–Muller space.

**Definition 1.4 (Parity-check rows).**

$$\forall n \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; \forall f \in \operatorname{V}\left(n\right) \to \operatorname{V}\left(n\right),\; \left(\forall e \in \operatorname{Monomials}\left(n, s\right),\; \forall x \in \operatorname{V}\left(n\right),\; \operatorname{parityMatrix}\left(n, s, f, \operatorname{inl}\left(e\right), x\right) = \prod_{i \in \operatorname{Fin}\left(n\right)} \operatorname{x}\left(i\right)^{\operatorname{val}\left(\operatorname{e}\left(i\right)\right)}\right) \land \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall x \in \operatorname{V}\left(n\right),\; \operatorname{parityMatrix}\left(n, s, f, \operatorname{inr}\left(i\right), x\right) = \operatorname{f}\left(x, i\right)\right)$$

*Formalization.* `D5/S3/Arith/SumFreeCodeDimensionRefutation.parityMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first rows evaluate all reduced monomials of the indicated degree. The remaining n rows are the coordinate functions of f. Redundant rows leave the kernel unchanged.

**Definition 1.5 (Parity-check linear map).**

$$\forall n \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; \forall f \in \operatorname{V}\left(n\right) \to \operatorname{V}\left(n\right),\; \forall w \in \operatorname{V}\left(n\right) \to \operatorname{ZMod}\left(3\right),\; \forall r \in \operatorname{Sum}\left(\operatorname{Monomials}\left(n, s\right), \operatorname{Fin}\left(n\right)\right),\; \operatorname{parityCheck}\left(n, s, f, w, r\right) = \sum_{x \in \operatorname{V}\left(n\right)} \operatorname{parityMatrix}\left(n, s, f, r, x\right) \cdot \operatorname{w}\left(x\right)$$

*Formalization.* `D5/S3/Arith/SumFreeCodeDimensionRefutation.parityCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word is sent to its scalar product with every parity-check row. The code consists of the words sent to zero.

**Definition 1.6 (Kernel dimension).**

$$\forall n \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; \forall f \in \operatorname{V}\left(n\right) \to \operatorname{V}\left(n\right),\; \operatorname{codeDim}\left(n, s, f\right) = \operatorname{finrank}\left(\operatorname{ZMod}\left(3\right), \operatorname{ker}\left(\operatorname{parityCheck}\left(n, s, f\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/SumFreeCodeDimensionRefutation.codeDim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The code dimension is the dimension over the ternary field of the kernel of this parity-check linear map.

**Definition 1.7 (Dimension independence assertion).**

$$claim \Leftrightarrow \left(\forall n \in \mathrm{Nat},\; \forall s \in \mathrm{Nat},\; 2 \le n \Rightarrow \left(1 \le s \Rightarrow \left(s \le n - 1 \Rightarrow \left(\forall f \in \operatorname{V}\left(n\right) \to \operatorname{V}\left(n\right),\; \forall g \in \operatorname{V}\left(n\right) \to \operatorname{V}\left(n\right),\; \operatorname{SumFree}\left(s, f\right) \Rightarrow \left(\operatorname{SumFree}\left(s, g\right) \Rightarrow \operatorname{codeDim}\left(n, s, f\right) = \operatorname{codeDim}\left(n, s, g\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/SumFreeCodeDimensionRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each admissible dimension and order, any two sum-free functions are asserted to give equal code dimensions.

**Theorem 1.8 (Dimension independence is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumFreeCodeDimensionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hou-zhao-2026-sum-free-code-dimension` (refuted) by `D5/S3/Arith/SumFreeCodeDimensionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hou-zhao-2026-sum-free-code-dimension","declaration_gid":"D5/S3/Arith/SumFreeCodeDimensionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

For n equal to two and s equal to one, take f(x,y) equal to (x squared plus y squared, zero) and g(x,y) equal to (x squared, y squared). Both sums on every affine line are nonzero. Their parity systems reduce to four and five independent rows respectively; explicit right inverses establish surjectivity. Rank–nullity gives code dimensions five and four.

## References

- Truth anchor: `D5/S3/Arith/SumFreeCodeDimensionRefutation.Monomials`
- Truth anchor: `D5/S3/Arith/SumFreeCodeDimensionRefutation.SumFree`
- Truth anchor: `D5/S3/Arith/SumFreeCodeDimensionRefutation.V`
- Truth anchor: `D5/S3/Arith/SumFreeCodeDimensionRefutation.claim`
- Truth anchor: `D5/S3/Arith/SumFreeCodeDimensionRefutation.codeDim`
- Truth anchor: `D5/S3/Arith/SumFreeCodeDimensionRefutation.parityCheck`
- Truth anchor: `D5/S3/Arith/SumFreeCodeDimensionRefutation.parityMatrix`
- Truth anchor: `D5/S3/Arith/SumFreeCodeDimensionRefutation.result`
