# History Kernel Extension

## Abstract

A fixed primitive kernel with universal square-residual extensions has positive finite tables and a positive free formal span.

**Definition 1.1 (The same kernel on every indexed list).**

$$\forall X: Type, \forall K: X \to X \to \mathbb{C}, \forall I: Type, \forall L: I \to X, \forall i: I, \forall j: I, \operatorname{finiteGram}\left(K, L, i, j\right) = \operatorname{K}\left(\operatorname{L}\left(i\right), \operatorname{L}\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Completion/HistoryKernelExtension.finiteGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The label type is arbitrary. The list need not be injective; repeated labels read identical entries of the same fixed K.

**Definition 1.2 (The complete extension block).**

$$\forall I: Type, [\operatorname{Fintype}\left(I\right)], \forall G: \operatorname{Matrix}\left(I, I, \mathbb{C}\right), \forall c: \operatorname{Matrix}\left(I, \operatorname{Unit}\left(\right), \mathbb{C}\right), \forall r: \mathbb{C}, \operatorname{residualExtension}\left(G, c, r\right) = \operatorname{fromBlocks}\left(G, G c, c^{*} G, c^{*} G c + \operatorname{constantMatrix}\left(r^{*} r\right)\right)$$

*Formalization.* `D5/S3/Quantum/Completion/HistoryKernelExtension.residualExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All four blocks are retained: G, Gc, conjugate-transpose(c)G, and conjugate-transpose(c)Gc plus conjugate(r)r. The index type is finite and may be empty. G may be singular and r may be zero.

**Definition 1.3 (The primitive universal extension law).**

$$\forall X: Type, \forall K: X \to X \to \mathbb{C}, \operatorname{KernelExtensionLaw}\left(K\right) = \forall n: \mathbb{N}, \forall L: \operatorname{Fin}\left(n\right) \to X, \forall h: X, \exists c: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Unit}\left(\right), \mathbb{C}\right), \exists r: \mathbb{C}, \operatorname{finiteGram}\left(K, \operatorname{append}\left(L, h\right)\right) = \operatorname{residualExtension}\left(\operatorname{finiteGram}\left(K, L\right), c, r\right)$$

*Formalization.* `D5/S3/Quantum/Completion/HistoryKernelExtension.KernelExtensionLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, every ordered n-label list L and every appended label h, some c and complex r give the displayed block equality. Sum.elim appends one Unit-indexed label while preserving every old entry. No symmetry, positivity, distinctness, vector space or nonzero residual is assumed.

**Theorem 1.4 (The extension law implies positivity on every finite list).**

$$\forall X: Type, \forall K: X \to X \to \mathbb{C}, \operatorname{KernelExtensionLaw}\left(K\right) \Rightarrow \forall n: \mathbb{N}, \forall L: \operatorname{Fin}\left(n\right) \to X, \operatorname{PosSemidef}\left(\operatorname{finiteGram}\left(K, L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/HistoryKernelExtension.extensionLaw_finiteGram_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction starts with the empty table. The successor step applies the actual law for K and uses the positive congruence of the old block and the scalar square. A reindexing recovers the given ordered list. Scalar Gram positivity and congruence are reused from Matrix.posSemidef_conjTranspose_mul_self and Matrix.PosSemidef.conjTranspose_mul_mul_same. This theorem is consumed by extensionLaw_kernel_posSemidef.

**Theorem 1.5 (The formal finitely supported span has a positive form).**

$$\forall X: Type, \forall K: X \to X \to \mathbb{C}, \operatorname{KernelExtensionLaw}\left(K\right) \Rightarrow \operatorname{PosSemidef}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/HistoryKernelExtension.extensionLaw_kernel_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Matrix.PosSemidef on the arbitrary label type means Hermitian symmetry and nonnegativity of the double kernel sum for every finitely supported complex coefficient family. The proof obtains symmetry from a two-label list and reduces each coefficient sum to its actual finite support. This supplies the positive-form input of C129 Theorem 2.4, without assuming a historical Hilbert space.

This module proves the forward implication of C129 Theorem 2.3. The converse construction for singular blocks, the certified-chain coverage criterion, and the label-preserving minimal Hilbert representation of Theorem 2.4 remain open here. No CP, Born or physical-control conclusion is inferred.

## References

- Truth anchor: `D5/S3/Quantum/Completion/HistoryKernelExtension.KernelExtensionLaw`
- Truth anchor: `D5/S3/Quantum/Completion/HistoryKernelExtension.extensionLaw_finiteGram_posSemidef`
- Truth anchor: `D5/S3/Quantum/Completion/HistoryKernelExtension.extensionLaw_kernel_posSemidef`
- Truth anchor: `D5/S3/Quantum/Completion/HistoryKernelExtension.finiteGram`
- Truth anchor: `D5/S3/Quantum/Completion/HistoryKernelExtension.residualExtension`
