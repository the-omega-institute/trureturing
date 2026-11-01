# Finite arithmetic kernels and finite output automata

## Abstract

Over every finite output alphabet, a sequence has finite arithmetic kernel exactly when a finite DFAO computes it on every least-significant-digit-first representation.

The characterization is Eilenberg's theorem. The Lean construction and its supporting declarations are transplanted from ATLAS, with their original proof bodies. This is verification and integration of that source, with no new-proof or mathematical novelty claim. Natural indices include zero. A digit word is read least significant digit first; its final digits are the high-order digits.

**Definition 1.1 (Value of a digit word).**

$$\forall k \in \mathrm{Nat},\; \forall ds \in \operatorname{List}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{Value}\left(k, ds\right) = \operatorname{foldr}\left(ds, (d: \operatorname{Fin}\left(k\right) \mapsto (v: \mathrm{Nat} \mapsto \operatorname{val}\left(d\right) + k \cdot v)), 0\right)$$

*Formalization.* `D5/S0/Automata/FiniteKernelDFAO.baseWordValueLSD` (`✓ std3`).

*Citation.* ATLAS contributors; Meta Platforms, Inc. and affiliates (2026). *Automatic sequences: finite kernels and the Eilenberg bridge*. URL: <https://github.com/facebookresearch/atlas-lean/blob/8c9ac8ce7d2febf34a232009e1e1b0a350174591/MathlibExt/Combinatorics/Words/Automatic.lean>.

*Commentary.*

For every natural base k and every finite word ds over Fin k, Value(k,ds) is its least-significant-digit-first value. The right fold starts at zero. Thus the empty word and every all-zero word represent zero; appending high-order zeros preserves value. The notation val(d) denotes the natural value of a digit d.

**Definition 1.2 (Correctness on every representation).**

$$\forall B \in \mathrm{Type},\; [\operatorname{Fintype}\left(B\right)] \forall k \in \mathrm{Nat},\; \forall a \in (\mathrm{Nat} \to B),\; (\operatorname{Machine}\left(k, a\right) \iff 2 \le k \land \left(\exists q \in \mathrm{Nat},\; 0 < q \land \left(\exists s \in \operatorname{Fin}\left(q\right),\; \exists t \in (\operatorname{Fin}\left(q\right) \to (\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(q\right))),\; \exists o \in (\operatorname{Fin}\left(q\right) \to B),\; \forall n \in \mathrm{Nat},\; \forall ds \in \operatorname{List}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{Value}\left(k, ds\right) = n \Rightarrow \operatorname{o}\left(\operatorname{Fold}\left(ds, t, s\right)\right) = \operatorname{a}\left(n\right)\right)\right))$$

*Formalization.* `D5/S0/Automata/FiniteKernelDFAO.IsKAutomaticSequence` (`✓ std3`).

*Citation.* ATLAS contributors; Meta Platforms, Inc. and affiliates (2026). *Automatic sequences: finite kernels and the Eilenberg bridge*. URL: <https://github.com/facebookresearch/atlas-lean/blob/8c9ac8ce7d2febf34a232009e1e1b0a350174591/MathlibExt/Combinatorics/Words/Automatic.lean>.

*Commentary.*

For a finite output type B, Machine(k,a) requires k at least two and a positive natural state count q, an initial state s, a total transition table t and an output map o. Fold(ds,t,s) is List.foldl: the leftmost, least significant digit is read first. Correctness quantifies over every natural n and every word of value n, including empty and padded representations. It imposes output invariance, not a zero self-loop at s.

**Definition 1.3 (Arithmetic kernel).**

$$\forall D \in \mathrm{Type}^{*},\; \forall k \in \mathrm{Nat},\; \forall a \in (\mathrm{Nat} \to D),\; \operatorname{Kernel}\left(k, a\right) = \{b: (\mathrm{Nat} \to D) \mid \exists e \in \mathrm{Nat},\; \exists r \in \mathrm{Nat},\; r < k^{e} \land b = (n: \mathrm{Nat} \mapsto \operatorname{a}\left(k^{e} \cdot n + r\right))\}$$

*Formalization.* `D5/S0/Automata/FiniteKernelDFAO.kKernel` (`✓ std3`).

*Citation.* ATLAS contributors; Meta Platforms, Inc. and affiliates (2026). *Automatic sequences: finite kernels and the Eilenberg bridge*. URL: <https://github.com/facebookresearch/atlas-lean/blob/8c9ac8ce7d2febf34a232009e1e1b0a350174591/MathlibExt/Combinatorics/Words/Automatic.lean>.

*Commentary.*

For any output type D in any universe, Kernel(k,a) consists of the decimations n ↦ a(k^e n+r), with natural exponent e and residue r less than k^e. No finiteness or additive structure on D is needed to define this set.

**Definition 1.4 (Finite-kernel automaticity).**

$$\forall D \in \mathrm{Type}^{*},\; \forall k \in \mathrm{Nat},\; \forall a \in (\mathrm{Nat} \to D),\; (\operatorname{Automatic}\left(k, a\right) \iff 2 \le k \land \operatorname{Finite}\left(\operatorname{Kernel}\left(k, a\right)\right))$$

*Formalization.* `D5/S0/Automata/FiniteKernelDFAO.IsKAutomatic` (`✓ std3`).

*Citation.* ATLAS contributors; Meta Platforms, Inc. and affiliates (2026). *Automatic sequences: finite kernels and the Eilenberg bridge*. URL: <https://github.com/facebookresearch/atlas-lean/blob/8c9ac8ce7d2febf34a232009e1e1b0a350174591/MathlibExt/Combinatorics/Words/Automatic.lean>.

*Commentary.*

Automatic(k,a) is the conjunction of k at least two and finiteness of the type of members of Kernel(k,a). This definition is available for arbitrary output types; the equivalence below retains the source's finite output type B : Type.

**Theorem 1.5 (One-digit kernel closure).**

$$\forall D \in \mathrm{Type}^{*},\; \forall q \in \mathrm{Nat},\; \forall a \in (\mathrm{Nat} \to D),\; \forall b \in (\mathrm{Nat} \to D),\; \forall j \in \mathrm{Nat},\; b \in \operatorname{Kernel}\left(q, a\right) \Rightarrow \left(j < q \Rightarrow (n: \mathrm{Nat} \mapsto \operatorname{b}\left(q \cdot n + j\right)) \in \operatorname{Kernel}\left(q, a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteKernelDFAO.chr_kernel_lam_mem` (`✓ std3`). ∎

*Citation.* ATLAS contributors; Meta Platforms, Inc. and affiliates (2026). *Automatic sequences: finite kernels and the Eilenberg bridge*. URL: <https://github.com/facebookresearch/atlas-lean/blob/8c9ac8ce7d2febf34a232009e1e1b0a350174591/MathlibExt/Combinatorics/Words/Automatic.lean>.

*Commentary.*

Decimating a kernel element b by a digit j less than q gives another member of the same q-kernel. The source constructs exponent e+1 and residue q^e j+R from a representation of b. This closure supplies the transition of the kernel-state machine.

**Theorem 1.6 (The original sequence is a kernel state).**

$$\forall D \in \mathrm{Type}^{*},\; \forall q \in \mathrm{Nat},\; \forall a \in (\mathrm{Nat} \to D),\; a \in \operatorname{Kernel}\left(q, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteKernelDFAO.chr_self_mem_kernel` (`✓ std3`). ∎

*Citation.* ATLAS contributors; Meta Platforms, Inc. and affiliates (2026). *Automatic sequences: finite kernels and the Eilenberg bridge*. URL: <https://github.com/facebookresearch/atlas-lean/blob/8c9ac8ce7d2febf34a232009e1e1b0a350174591/MathlibExt/Combinatorics/Words/Automatic.lean>.

*Commentary.*

The exponent zero and residue zero put every sequence a in its own q-kernel, even for bases zero and one. For the final theorem this state provides the initial state and certifies that the finite state count is positive.

**Theorem 1.7 (Eilenberg's finite-kernel equivalence).**

$$\forall B \in \mathrm{Type},\; [\operatorname{Fintype}\left(B\right)] \forall k \in \mathrm{Nat},\; \forall a \in (\mathrm{Nat} \to B),\; (2 \le k \land \operatorname{Finite}\left(\operatorname{Kernel}\left(k, a\right)\right) \iff 2 \le k \land \left(\exists q \in \mathrm{Nat},\; 0 < q \land \left(\exists s \in \operatorname{Fin}\left(q\right),\; \exists t \in (\operatorname{Fin}\left(q\right) \to (\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(q\right))),\; \exists o \in (\operatorname{Fin}\left(q\right) \to B),\; \forall n \in \mathrm{Nat},\; \forall ds \in \operatorname{List}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{Value}\left(k, ds\right) = n \Rightarrow \operatorname{o}\left(\operatorname{Fold}\left(ds, t, s\right)\right) = \operatorname{a}\left(n\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteKernelDFAO.isKAutomatic_iff_isKAutomaticSequence` (`✓ std3`). ∎

*Citation.* Boris Adamczewski and Jason P. Bell (2012). *On vanishing coefficients of algebraic power series over fields of positive characteristic*. URL: <https://arxiv.org/abs/1205.4091v1>.

*Commentary.*

For every finite B : Type, every natural k and every sequence a : Nat → B, Automatic(k,a) is equivalent to Machine(k,a). Both sides contain the conjunct 2 ≤ k. In the forward direction the states are exactly the kernel elements, relabeled by an equivalence with Fin q; the initial state is a, a digit acts by decimation, and the output is evaluation at zero. The inductive chr_fold_val invariant identifies the reached state with n ↦ b(k^length(ds) n+Value(k,ds)). In the reverse direction, fix a representing word for each n. A kernel element with exponent e and residue r is realized by the state reached after a representing word for r of length exactly e. Padding by high-order zeros supplies that exact length. Concatenating this word with a representing word for n yields k^e n+r, so all kernel elements lie in the finite image of the q states.

The supplied ATLAS revision is 8c9ac8ce7d2febf34a232009e1e1b0a350174591. Only the two kernel definitions, Automatic's live declarations from chr_kernel_lam_mem through the equivalence, and CobhamUniformMorphism's two digit/DFAO definitions are retained. The unrelated power-base and morphic-word declarations are excluded. Packaging changes are the namespace, module/public-section removal and explicit digit-lemma import. Meta Platforms, Inc. and affiliates retain copyright and all rights reserved; the full source license, including the intended-use preface, is the existing docs/reports/lovasz-suppliers/atlas-LICENSE.txt. The pinned source tree has no NOTICE file.

This integration verifies mathematics and supplies no ML training, fine-tuning, distillation, evaluation or development pipeline. The license text and its notice are preserved; no general legal-clearance claim is made. Retire the transplant when this repository's actually adopted Mathlib pin supplies an equivalent finite-alphabet theorem on every LSDF representation, and then use that theorem directly.

The final theorem supplies neither an arbitrary-output extension, a most-significant-digit interface, a canonical-word-only interface, nor an initial-state zero self-loop. The integer-valued k-regularity results and the Simon/Hunter results are separate. No equivalence with their interfaces is asserted here.

## References

- Truth anchor: `D5/S0/Automata/FiniteKernelDFAO.IsKAutomatic`
- Truth anchor: `D5/S0/Automata/FiniteKernelDFAO.IsKAutomaticSequence`
- Truth anchor: `D5/S0/Automata/FiniteKernelDFAO.baseWordValueLSD`
- Truth anchor: `D5/S0/Automata/FiniteKernelDFAO.chr_kernel_lam_mem`
- Truth anchor: `D5/S0/Automata/FiniteKernelDFAO.chr_self_mem_kernel`
- Truth anchor: `D5/S0/Automata/FiniteKernelDFAO.isKAutomatic_iff_isKAutomaticSequence`
- Truth anchor: `D5/S0/Automata/FiniteKernelDFAO.kKernel`
