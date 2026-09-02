# Readout-Update Commutator Factorization

## Abstract

The readout-update commutator factors on its common domain and has the exact defect norm when bounded.

**Theorem 1.1 (The commutator factors and has the defect norm).**

$$\forall I : Type, tau : \operatorname{Perm}(I), f : I \to \mathbb{C},\\{}\operatorname{readoutUpdateCommutator}(tau, f) = \operatorname{factoredReadoutUpdateCommutator}(tau, f) \land\\{}\forall h : \operatorname{Finite}(I) \lor \operatorname{MemLp}(f, \infty), \Vert \operatorname{boundedReadoutUpdateCommutator}(tau, f, h) \Vert = \Vert \operatorname{boundedReadoutDefect}(tau, f, h) \Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization.readout_update_commutator_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be an address type, tau a reversible address permutation, and f a complex readout coefficient. The first conjunct identifies the independently constructed commutator with multiplication by the update defect after the update, on their natural common domain.

For every proof that I is finite or f belongs to lp infinity, the second conjunct states that the norm of the bounded commutator is exactly the lp-infinity norm of the bundled update defect.

## References

- Truth anchor: `D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization.readout_update_commutator_factorization`
