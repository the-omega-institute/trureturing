# Zero Memory Criterion

## Abstract

The all-future kernel is the maximal invariant part of the current kernel, and its quotient vanishes exactly when the dynamics descends through the observation.

**Theorem 1.1 (The eventual kernel is currently invisible).**

$$\forall K, V, W, C, T, \operatorname{LinearSetup}\left(K, V, W, C, T\right) \Rightarrow \left(N_{\infty}\right)\left(C, T\right) \subseteq \operatorname{ker}\left(C\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.eventualKernel_le_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership at iterate zero is exactly membership in the current kernel. Thus every direction invisible at all future times is invisible now.

**Theorem 1.2 (The eventual kernel is invariant).**

$$\forall x, x \in \left(N_{\infty}\right)\left(C, T\right) \Rightarrow T\left(x\right) \in \left(N_{\infty}\right)\left(C, T\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.eventualKernel_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the update shifts every required future-kernel test forward by one step, so all tests remain satisfied.

**Theorem 1.3 (The eventual kernel is the maximal invariant invisible submodule).**

$$\forall M, (M \subseteq \operatorname{ker}\left(C\right) \land \operatorname{map}\left(T, M\right) \subseteq M) \Rightarrow M \subseteq \left(N_{\infty}\right)\left(C, T\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.eventualKernel_is_greatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any submodule M contained in the current kernel and preserved by T, induction keeps every finite iterate of each element inside M. Hence M lies in the all-future kernel.

**Theorem 1.4 (The memory quotient is zero exactly at kernel equality).**

$$\operatorname{Subsingleton}\left(N_{0}/N_{\infty}\right) \Leftrightarrow \left(N_{\infty}\right)\left(C, T\right) = \operatorname{ker}\left(C\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.zero_memory_iff_eventualKernel_eq_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The memory object is the quotient of the current kernel by the eventual kernel pulled back to that subtype. Mathlib's quotient subsingleton criterion reduces triviality to the denominator being top, which is equivalent to equality of the two kernels.

**Theorem 1.5 (Zero memory, kernel invariance, and exact descent).**

$$\operatorname{TFAE}\left(\operatorname{Subsingleton}\left(N_{0}/N_{\infty}\right), \operatorname{map}\left(T, \operatorname{ker}\left(C\right)\right) \subseteq \operatorname{ker}\left(C\right), \exists Tbar: W \to W, \forall x, C\left(T\left(x\right)\right) = Tbar\left(C\left(x\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.zero_memory_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a division ring, V and W be K-modules, C the observation, and T the update. Zero memory means that the quotient of the current kernel by the all-future kernel is a singleton.

Kernel invariance first induces a linear map on the realized range of C through the first isomorphism theorem. The vector-space extension theorem then extends it to an endomorphism of all W, giving the literal whole-codomain descent required by the source statement.

Conversely, a commuting whole-space descent sends every zero observation to zero after one update. The proof also verifies zero source or target modules, zero or injective observation, and zero or identity dynamics as degenerate cases.

**Theorem 1.6 (A general ring does not support whole-space descent).**

$$\exists C, T: \mathbb{Z}\times\mathbb{Z} \to \mathbb{Z}\times\mathbb{Z}, \operatorname{map}\left(T, \operatorname{ker}\left(C\right)\right) \subseteq \operatorname{ker}\left(C\right) \land \neg\exists Tbar: \mathbb{Z}\times\mathbb{Z} \to \mathbb{Z}\times\mathbb{Z}, \forall x, C\left(T\left(x\right)\right) = Tbar\left(C\left(x\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.division_ring_assumption_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over the integers, take C(a,b)=(2a,b) and let T swap the coordinates. The observation is injective, so its kernel is invariant. A descended integer-linear map would have to send (2,0) to (0,1), contradicting linearity because the second coordinate of twice any vector is even.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.division_ring_assumption_is_necessary`
- Truth anchor: `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.eventualKernel_invariant`
- Truth anchor: `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.eventualKernel_is_greatest`
- Truth anchor: `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.eventualKernel_le_ker`
- Truth anchor: `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.zero_memory_criterion`
- Truth anchor: `D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.zero_memory_iff_eventualKernel_eq_ker`
