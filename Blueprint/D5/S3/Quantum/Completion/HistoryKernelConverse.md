# Singular History Extensions and Certified Finite Covers

## Abstract

A positive primitive history kernel admits singular square-residual extensions; finite-set coverage by certified chains is sufficient for the universal law.

**Theorem 1.1 (All ordered finite tables characterize the extension law).**

$$\forall X: Type, \forall K: X \to X \to \mathbb{C}, \operatorname{KernelExtensionLaw}\left(K\right) \Leftrightarrow \forall n: \mathbb{N}, \forall L: \operatorname{Fin}\left(n\right) \to X, \operatorname{PosSemidef}\left(\operatorname{finiteGram}\left(K, L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/HistoryKernelConverse.extensionLaw_iff_finiteGram_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward implication uses HistoryKernelExtension.extensionLaw_finiteGram_posSemidef. For the reverse, the actual appended Gram table is positive. Its cross-column lies in the range of its old block, even when that block is singular. Choose c with b = Gc, and apply positive congruence to the column (-c,1). The resulting scalar is the actual difference d - conjugate-transpose(c)Gc, so it is real and nonnegative. Its nonnegative real square root, embedded in the complex numbers, gives r. Hermitian symmetry then supplies the original lower cross-block, and the resulting equality retains all four actual blocks.

**Theorem 1.2 (The global positive form characterizes the extension law).**

$$\forall X: Type, \forall K: X \to X \to \mathbb{C}, \operatorname{KernelExtensionLaw}\left(K\right) \Leftrightarrow \operatorname{PosSemidef}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/HistoryKernelConverse.extensionLaw_iff_kernel_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary label type, Matrix.PosSemidef includes Hermitian symmetry and positivity on finitely supported coefficient families. Its finite restrictions give every ordered Gram table, with repeated labels allowed. In the other direction the existing forward theorem supplies the global positive form. This equivalence is used to recover the extension law from certified finite covers.

**Definition 1.3 (A certificate starts at the empty table and retains each extension equality).**

$$\forall X: Type, \forall K: X \to X \to \mathbb{C}, (\forall L: \operatorname{Fin}\left(0\right) \to X, \operatorname{CertifiedHistory}\left(K, 0, L\right) = (\operatorname{True}\left(\right))) \land (\forall n: \mathbb{N}, \forall L: \operatorname{Fin}\left(n + 1\right) \to X, \operatorname{CertifiedHistory}\left(K, n + 1, L\right) = ((\operatorname{CertifiedHistory}\left(K, n, \operatorname{tail}\left(L\right)\right)) \land (\exists c: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Unit}\left(\right), \mathbb{C}\right), \exists r: \mathbb{C}, \operatorname{finiteGram}\left(K, \operatorname{append}\left(\operatorname{tail}\left(L\right), \operatorname{head}\left(L\right)\right)\right) = (\operatorname{residualExtension}\left(\operatorname{finiteGram}\left(K, \operatorname{tail}\left(L\right)\right), c, r\right)))))$$

*Formalization.* `D5/S3/Quantum/Completion/HistoryKernelConverse.CertifiedHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero-length certificate is True. For a successor list, tail(L)(i) = L(i.succ) is certified and the actual Sum.elim table appending L(0) to that tail equals residualExtension of the tail table for some c and r. Reindexing puts the newly appended Unit coordinate at index zero of the given list. This records an actual sequence of the primitive block equalities; no positivity premise is inserted.

**Definition 1.4 (Every finite label set is contained in a certified history).**

$$\forall X: Type, \forall K: X \to X \to \mathbb{C}, \operatorname{CertifiedFiniteCover}\left(K\right) = (\forall s: \operatorname{Finset}\left(X\right), \exists n: \mathbb{N}, \exists L: \operatorname{Fin}\left(n\right) \to X, (\operatorname{CertifiedHistory}\left(K, n, L\right)) \land (\forall x: X, x \in s \Rightarrow \exists i: \operatorname{Fin}\left(n\right), \operatorname{L}\left(i\right) = (x)))$$

*Formalization.* `D5/S3/Quantum/Completion/HistoryKernelConverse.CertifiedFiniteCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each finite set may have its own certified chain. The certificate may contain extra labels and repeats. There is no assumption of one countable log covering the entire label type.

**Theorem 1.5 (A certified finite cover supplies the universal extension law).**

$$\forall X: Type, \forall K: X \to X \to \mathbb{C}, \operatorname{CertifiedFiniteCover}\left(K\right) \Rightarrow \operatorname{KernelExtensionLaw}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/HistoryKernelConverse.certifiedFiniteCover_extensionLaw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on each individual certificate proves positivity of its actual terminal table, using the original residual-extension positivity lemma. Given any ordered finite list, take a certified chain covering its label set and choose a position for each requested label. Pullback of the terminal table gives the requested Gram table, including repeated requested labels. The finite-support positive-form supplier then yields the global positive kernel, and the preceding equivalence supplies every same-entry extension witness.

## Application: a single finite-test schema

For an arbitrary finite complex table M, define its entire quadratic evaluation Q_M(z)=sum_{i,j} conjugate(z_i) M_{ij} z_j. If Q_M(z) is real for every complex coefficient vector z, M is Hermitian. If Q_M(z) is real and nonnegative for every z, M is positive semidefinite. Reality of the whole complex value is essential: a nonnegative real part alone does not suffice. For example M=[i] passes that real-part inequality for every z, but M is not Hermitian.

$$
\forall z: I \to \mathbb{C}, (\operatorname{ofReal}\left(\operatorname{Re}\left(\operatorname{quadraticEvaluation}\left(M, z\right)\right)\right) = (\operatorname{quadraticEvaluation}\left(M, z\right))) \land (0 \le \operatorname{Re}\left(\operatorname{quadraticEvaluation}\left(M, z\right)\right))
$$

These implications directly reuse Mathlib LinearMap.isSymmetric_iff_inner_map_self_real and LinearMap.isPositive_iff_complex through Matrix.isSymmetric_toEuclideanLin_iff and Matrix.isPositive_toEuclideanLin_iff. The first implication supplies endpoint conjugation instead of assuming it as a separate clause. The test already presupposes complex-valued entries and arbitrary complex coefficient vectors; it does not derive the complex field or an operational superposition mechanism.

For one common kernel K on the entire label type, impose this same evaluation condition on every finite ordered label family and every complex coefficient vector. The resulting positive finiteGram tables give KernelExtensionLaw through extensionLaw_iff_finiteGram_posSemidef. Repeated labels and empty families remain allowed. The universal schema is not one finite experiment, and separately chosen tables cannot substitute for restrictions of the same K. A label-preserving Hilbert realization still uses the separate common-kernel completion construction, such as RKHS.OfKernel; these finite tests do not themselves specify physical operations.

Two-label legality alone is insufficient. The real symmetric three-label table with diagonal 1 and every off-diagonal -1 has positive semidefinite two-label restrictions, including repeated-label restrictions. At z=(1,1,1), its entire quadratic evaluation is -3, so the three-label table is not positive semidefinite. Pairwise comparisons therefore do not settle simultaneous finite consistency.

Counting clauses does not show that raw complex positivity is logically weaker than the original three-way characterization: their objects and premises differ. Endpoint reversal K(y,x)=conjugate(K(x,y)) is also distinct from reversing a sequence of measurements. No commutation of measurement updates, operational preparations, Born interpretation, tensor composition, or dynamics follows here.

白话：每两项单独看都合法，放到一起仍可能矛盾。更准确的简洁要求是：同一张比较表的每个有限部分，对所有复系数作整体检验都得到非负实数；反向比较的共轭关系会随之成立。这是一条普遍检验规则，不是一次有限实验，也还不是量子力学的完整起源。

The block range and finite-support suppliers are adapted from TauCetiProject/TauCeti at revision 52f9d081237dadaf6d4eae13629281f7faa37d54, specifically LinearAlgebra/Matrix/PosSemidef.lean and Analysis/Matrix/PosSemidef/Block.lean. They implement standard positive block matrix facts. All results allow empty index types, singular and zero old blocks, zero diagonals and zero residuals. When the history type is empty, the extension obligation has no appended label and is vacuous.

Certification of a single log only establishes positivity for its represented labels; the finite-cover quantifier is essential for a conclusion on the whole declared label type. The label-preserving minimal Hilbert representation and its uniqueness require the separate completion argument. No CP, Born, physical control or empirical realization follows from the kernel equivalences alone.

## References

- Truth anchor: `D5/S3/Quantum/Completion/HistoryKernelConverse.CertifiedFiniteCover`
- Truth anchor: `D5/S3/Quantum/Completion/HistoryKernelConverse.CertifiedHistory`
- Truth anchor: `D5/S3/Quantum/Completion/HistoryKernelConverse.certifiedFiniteCover_extensionLaw`
- Truth anchor: `D5/S3/Quantum/Completion/HistoryKernelConverse.extensionLaw_iff_finiteGram_posSemidef`
- Truth anchor: `D5/S3/Quantum/Completion/HistoryKernelConverse.extensionLaw_iff_kernel_posSemidef`
- Dependency: [D5/S3/Quantum/Completion/HistoryKernelExtension](HistoryKernelExtension.md)
