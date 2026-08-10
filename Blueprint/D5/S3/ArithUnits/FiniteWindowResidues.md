# Finite-Window Residue Realization

## Abstract

Every finite coprime residue window has a bounded simultaneous representative.

**Theorem 1.1 (Every finite pairwise-coprime residue window is realizable).**

$$\forall W,a,m,\ \operatorname{pairwiseCoprime}(m,W) \land (\forall i\in W,\ m_i \neq 0) \Rightarrow \exists n<\prod_{i\in W}m_i,\ \forall i\in W,\ n \equiv a_i\ (\operatorname{mod}\ m_i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/FiniteWindowResidues.finite_window_residues_realizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite window of indices, a nonzero modulus at each index, and an arbitrary target residue at each index. When the window's moduli are pairwise coprime, one natural number realizes every target congruence simultaneously. The witness is bounded strictly below the product of the moduli, making the finite period explicit rather than asserting only an unbounded existence claim.

The library was searched before proving. Pinned Mathlib supplies the simultaneous witness as Nat.chineseRemainderOfFinset and proves its product bound as Nat.chineseRemainderOfFinset_lt_prod. The Lean declaration is therefore a thin honest wrapper that packages those two facts into the source atom's finite-window realization form. The source's concrete residue scan is treated as an illustrative certificate and is not promoted into the universal theorem.

## References

- Truth anchor: `D5/S3/ArithUnits/FiniteWindowResidues.finite_window_residues_realizable`
