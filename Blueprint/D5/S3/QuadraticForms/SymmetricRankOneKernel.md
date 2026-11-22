# Symmetric rank-one kernel transitions

## Abstract

A real symmetric rank-one update has three exact transitions for its kernel and scalar response.

Let B be a symmetric linear map on a real inner-product space E and e a direction in E. Write U for the map x ↦ Bx + t ⟨e,x⟩e, and write k(B) for the real finrank of its kernel. A flagged state has a kernel vector whose pairing with e is nonzero. A scalar response g means that By = e has a solution and that every solution has pairing g with e.

Finite dimensionality is required for the exhaustive state split and the two nullity changes. The symmetry law and the nonresonant kernel identity hold on an arbitrary real inner-product space.

**Definition 1.1 (Nonzero pairing in the kernel).**

$$\operatorname{Flag}\left(B, e\right) \iff \exists z \in \operatorname{ker}\left(B\right), \langle e,z\rangle \neq 0$$

*Formalization.* `D5/S3/QuadraticForms/SymmetricRankOneKernel.HasNonzeroPairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witness lies in the actual kernel and pairs nontrivially with the given direction.

**Definition 1.2 (Scalar response to the update direction).**

$$\operatorname{Response}\left(B, e, g\right) \iff (\exists y, \operatorname{B}\left(y\right)=e) \land (\forall y, \operatorname{B}\left(y\right)=e \Rightarrow \langle e,y\rangle=g)$$

*Formalization.* `D5/S3/QuadraticForms/SymmetricRankOneKernel.ScalarResponse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existence clause prevents a vacuous response for an inconsistent right-hand side.

**Definition 1.3 (Symmetric rank-one update).**

$$\operatorname{U}\left(x\right)=\operatorname{B}\left(x\right)+t\langle e,x\rangle e$$

*Formalization.* `D5/S3/QuadraticForms/SymmetricRankOneKernel.update` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The update direction appears in both the linear functional and the displaced vector.

**Theorem 1.4 (Symmetry of the update).**

$$\operatorname{Symmetric}\left(B\right) \Rightarrow \operatorname{Symmetric}\left(U\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneKernel.update_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic contribution to the bilinear pairing is symmetric in its two arguments.

**Theorem 1.5 (Solvability and vanishing kernel pairings).**

$$(\exists y, \operatorname{B}\left(y\right)=e) \iff \neg\operatorname{Flag}\left(B, e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneKernel.solvable_iff_no_nonzero_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite-dimensional E, the range of B is the orthogonal complement of its kernel.

**Theorem 1.6 (The exhaustive kernel and response states).**

$$\operatorname{Flag}\left(B, e\right) \lor (\exists! g, \operatorname{Response}\left(B, e, g\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneKernel.nonzero_pairing_or_unique_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In finite dimension, solvability supplies a response whenever the flag is absent. Two solutions differ by a kernel vector and have the same pairing.

**Theorem 1.7 (Nullity loss from a flagged kernel).**

$$\operatorname{k}\left(U\right)+1=\operatorname{k}\left(B\right) \land \operatorname{Response}\left(U, e, \frac{1}{t}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneKernel.update_of_nonzero_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In finite dimension, assume the flag for B and t ≠ 0. Pairing the new kernel equation with the flagged vector cuts out the kernel of one nonzero functional on ker B. Scaling that vector supplies a solution of Uy = e with response 1/t.

**Theorem 1.8 (Nullity gain at scalar resonance).**

$$\operatorname{k}\left(U\right)=\operatorname{k}\left(B\right)+1 \land \operatorname{Flag}\left(U, e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneKernel.update_of_resonance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In finite dimension, assume response g for B and 1 + tg = 0. A solution of By = e lies in the new kernel with nonzero pairing g. It adds one direction to the old kernel.

**Theorem 1.9 (Kernel preservation away from resonance).**

$$\operatorname{ker}\left(U\right)=\operatorname{ker}\left(B\right) \land \operatorname{Response}\left(U, e, \frac{g}{1+tg}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneKernel.update_of_nonresonance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume response g for B and 1 + tg ≠ 0. The kernel equation forces zero pairing, and scaling a solution of By = e by the reciprocal of the resonance factor gives the new response.

**Definition 1.10 (Block-diagonal linear map).**

$$\operatorname{D}\left(x, i\right)=\operatorname{A}\left(i, \operatorname{x}\left(i\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/SymmetricRankOneKernel.blockDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the Euclidean product, the map acts on each coordinate by that coordinate's block.

**Theorem 1.11 (Kernel and response states of a block sum).**

$$\operatorname{Symmetric}\left(D\right) \land \operatorname{k}\left(D\right)=\sum \operatorname{k}\left(\operatorname{A}\left(i\right)\right) \land (\operatorname{Flag}\left(D, u\right) \iff \exists i, \operatorname{Flag}\left(\operatorname{A}\left(i\right), \operatorname{u}\left(i\right)\right)) \land (\forall g, (\forall i, \operatorname{Response}\left(\operatorname{A}\left(i\right), \operatorname{u}\left(i\right), \operatorname{g}\left(i\right)\right)) \Rightarrow \operatorname{Response}\left(D, u, \sum \operatorname{g}\left(i\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneKernel.blockDiagonal_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family of finite-dimensional symmetric blocks A with direction u in the Euclidean product, D is symmetric, its nullity is the sum of the child nullities, and its flag is equivalent to the existence of a child flag. If every child has scalar response g(i) at direction u(i), then D has response equal to their sum. The kernel is a product and the inner product is a sum of coordinate pairings.

## References

- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.HasNonzeroPairing`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.ScalarResponse`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.blockDiagonal`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.blockDiagonal_states`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.nonzero_pairing_or_unique_scalar`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.solvable_iff_no_nonzero_pairing`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.update`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.update_of_nonresonance`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.update_of_nonzero_pairing`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.update_of_resonance`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneKernel.update_symmetric`
